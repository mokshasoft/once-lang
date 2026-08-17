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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Codegen.ShapeTable
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStackPtr
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockStep
d_BlockStep_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 -> ()
d_BlockStep_34 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockStepAt
d_BlockStepAt_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 -> ()
d_BlockStepAt_36 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps
d_BlockSteps_38 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr
d_CompiledCorr_42 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Emitted
d_Emitted_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] -> ()
d_Emitted_46 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.EntryLike
d_EntryLike_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_48 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv
d_FlatInv_50 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Reachable
d_Reachable_54 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt
d_RunAt_56 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckAt
d_StuckAt_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] -> AgdaAny -> ()
d_StuckAt_60 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckSteps
d_StuckSteps_62 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply
d_Supply_66 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.above-frontier-disj
d_above'45'frontier'45'disj_70 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_above'45'frontier'45'disj_70 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.all-headView
d_all'45'headView_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_all'45'headView_72 v8
du_all'45'headView_72 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_72 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_all'45'headView_942
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_headView_182
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.blk-len
d_blk'45'len_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer
d_blk'45'len_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_blk'45'len_74 v8
du_blk'45'len_74 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer
du_blk'45'len_74 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.blk-off
d_blk'45'off_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> Integer
d_blk'45'off_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_blk'45'off_76 v8
du_blk'45'off_76 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> Integer
du_blk'45'off_76 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.blk-off-suc
d_blk'45'off'45'suc_78 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'45'off'45'suc_78 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.block-run-exec
d_block'45'run'45'exec_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'run'45'exec_80 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-alloc-heap
d_bs'45'alloc'45'heap_82 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'alloc'45'heap_82 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2046
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-branch-nz
d_bs'45'c'45'branch'45'nz_84 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'nz_84 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1856
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-branch-scratch-zero
d_bs'45'c'45'branch'45'scratch'45'zero_86 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'scratch'45'zero_86 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1842
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-branch-tag-nz
d_bs'45'c'45'branch'45'tag'45'nz_88 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'nz_88 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1890
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-branch-tag-zero
d_bs'45'c'45'branch'45'tag'45'zero_90 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'zero_90 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1874
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-jmp
d_bs'45'c'45'jmp_92 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'jmp_92 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1826
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-label
d_bs'45'c'45'label_94 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'label_94 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1556
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-ret
d_bs'45'c'45'ret_96 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [Integer] ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'ret_96 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_1962
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-c-thunk
d_bs'45'c'45'thunk_98 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'thunk_98 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1940
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-call
d_bs'45'call_100 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'call_100 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2022
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-count-inc
d_bs'45'count'45'inc_102 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'inc_102 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1914
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-count-zero
d_bs'45'count'45'zero_104 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'zero_104 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1534
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-lea-slot
d_bs'45'lea'45'slot_106 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'lea'45'slot_106 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1604
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-code-addr
d_bs'45'load'45'code'45'addr_108 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'code'45'addr_108 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2000
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-const
d_bs'45'load'45'const_110 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const_110 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_1974
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-const-float
d_bs'45'load'45'const'45'float_112 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const'45'float_112 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_1986
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-from-slot
d_bs'45'load'45'from'45'slot_114 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'from'45'slot_114 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1700
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-indirect
d_bs'45'load'45'indirect_116 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect_116 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1640
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-indirect-stack
d_bs'45'load'45'indirect'45'stack_118 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'stack_118 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1656
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-indirect-suc
d_bs'45'load'45'indirect'45'suc_120 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc_120 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1670
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-indirect-suc-stack
d_bs'45'load'45'indirect'45'suc'45'stack_122 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc'45'stack_122 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1686
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-load-tag-lit
d_bs'45'load'45'tag'45'lit_124 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'tag'45'lit_124 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1626
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-mov-input2-to-output
d_bs'45'mov'45'input2'45'to'45'output_126 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'input2'45'to'45'output_126 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'input2'45'to'45'output_1494
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-mov-output-to-input2
d_bs'45'mov'45'output'45'to'45'input2_128 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'output'45'to'45'input2_128 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'output'45'to'45'input2_1504
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-mov-to-input
d_bs'45'mov'45'to'45'input_130 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'input_130 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1484
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-mov-to-output
d_bs'45'mov'45'to'45'output_132 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'output_132 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1474
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-reclaim-to
d_bs'45'reclaim'45'to_134 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'reclaim'45'to_134 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1568
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-restore-input
d_bs'45'restore'45'input_136 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'restore'45'input_136 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1714
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-save-closure-reg
d_bs'45'save'45'closure'45'reg_138 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'save'45'closure'45'reg_138 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1614
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-scratch-dec
d_bs'45'scratch'45'dec_140 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'dec_140 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1902
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-scratch-load-count
d_bs'45'scratch'45'load'45'count_142 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'load'45'count_142 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-scratch-one
d_bs'45'scratch'45'one_144 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'one_144 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-scratch-zero
d_bs'45'scratch'45'zero_146 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'zero_146 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-store-at-slot
d_bs'45'store'45'at'45'slot_148 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'at'45'slot_148 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-store-indirect
d_bs'45'store'45'indirect_150 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect_150 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1768
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-store-indirect-stack
d_bs'45'store'45'indirect'45'stack_152 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'stack_152 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1784
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-store-indirect-suc
d_bs'45'store'45'indirect'45'suc_154 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'suc_154 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1796
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-store-indirect-suc-stack
d_bs'45'store'45'indirect'45'suc'45'stack_156 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'suc'45'stack_156 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1812
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-worklist-check
d_bs'45'worklist'45'check_158 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'check_158 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1592
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-worklist-init
d_bs'45'worklist'45'init_160 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'init_160 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1580
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-worklist-pop
d_bs'45'worklist'45'pop_162 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'pop_162 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1728
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.bs-worklist-push
d_bs'45'worklist'45'push_164 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'push_164 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1756
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.code-eq
d_code'45'eq_166 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_166 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.cons-step
d_cons'45'step_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'step_168 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.dataCorr
d_dataCorr_170 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_dataCorr_170 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.drop-+
d_drop'45''43'_172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_172 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.drop-[]
d_drop'45''91''93'_174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_174 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.drop-compile
d_drop'45'compile_176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_176 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.drop-fetch
d_drop'45'fetch_178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_178 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.drop-len-++
d_drop'45'len'45''43''43'_180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_180 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.event-of-pure
d_event'45'of'45'pure_182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_event'45'of'45'pure_182 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.events-running-end
d_events'45'running'45'end_184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'end_184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_events'45'running'45'end_184
du_events'45'running'45'end_184 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'end_184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_events'45'running'45'end_1246
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-at-offset
d_fetch'45'at'45'offset_186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_186 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-2nd
d_fetch'45'block'45'2nd_188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_188 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-3rd
d_fetch'45'block'45'3rd_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_190 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-4th
d_fetch'45'block'45'4th_192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_192 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-5th
d_fetch'45'block'45'5th_194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_194 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-6th
d_fetch'45'block'45'6th_196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_196 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-head
d_fetch'45'block'45'head_198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_198 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-block-nth
d_fetch'45'block'45'nth_200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'nth_200 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-drop
d_fetch'45'drop_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [AgdaAny] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_202 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-just-drop
d_fetch'45'just'45'drop_204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'just'45'drop_204 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch-nothing-drop
d_fetch'45'nothing'45'drop_206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'nothing'45'drop_206 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label-corr
d_find'45'label'45'corr_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_208 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label-go-skip
d_find'45'label'45'go'45'skip_210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [AgdaAny] ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_210 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label-none-corr
d_find'45'label'45'none'45'corr_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_212 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label-none-go
d_find'45'label'45'none'45'go_214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_214 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label-pres
d_find'45'label'45'pres_216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_find'45'label'45'pres_216
du_find'45'label'45'pres_216 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_216 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'label'45'pres_788
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-thunk-corr
d_find'45'thunk'45'corr_218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_218 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-thunk-pres
d_find'45'thunk'45'pres_220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_find'45'thunk'45'pres_220
du_find'45'thunk'45'pres_220 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_220 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'thunk'45'pres_616
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-inv-step
d_flat'45'inv'45'step_222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050
d_flat'45'inv'45'step_222 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10
  = du_flat'45'inv'45'step_222 v1
du_flat'45'inv'45'step_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050
du_flat'45'inv'45'step_222 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1096
      (coe v0) v3 v4 v5 v8
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.hit-labelled
d_hit'45'labelled_224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hit'45'labelled_224 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.inv-closure
d_inv'45'closure_226 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  AgdaAny
d_inv'45'closure_226 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1074
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.inv-env
d_inv'45'env_228 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_228 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.inv-ev
d_inv'45'ev_230 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_230 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.inv-regtag
d_inv'45'regtag_232 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_394
d_inv'45'regtag_232 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'regtag_1076
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.inv-run
d_inv'45'run_234 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288
d_inv'45'run_234 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.inv-wf
d_inv'45'wf_236 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586
d_inv'45'wf_236 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.just-inj
d_just'45'inj_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_238 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.pc-off
d_pc'45'off_244 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_244 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.ret-eq
d_ret'45'eq_250 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  AgdaAny
d_ret'45'eq_250 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_694
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-emit
d_run'45'emit_252 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_252 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-emitted
d_run'45'emitted_254 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_254 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_302
         (coe v0))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-heap
d_run'45'heap_256 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  AgdaAny
d_run'45'heap_256 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'heap_306
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-ir
d_run'45'ir_258 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_258 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_302
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-reach
d_run'45'reach_260 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_262
d_run'45'reach_260 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_308
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sigop-concrete-fetch
d_sigop'45'concrete'45'fetch_262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'concrete'45'fetch_262 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sigop-run-arith
d_sigop'45'run'45'arith_264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'run'45'arith_264 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sigop-run-external
d_sigop'45'run'45'external_266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'run'45'external_266 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.skip-labelled
d_skip'45'labelled_268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'labelled_268 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.skip-plain
d_skip'45'plain_270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'plain_270 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.slot-heap-disj
d_slot'45'heap'45'disj_272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'heap'45'disj_272 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.st-c-branch-scratch-zero
d_st'45'c'45'branch'45'scratch'45'zero_274 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'branch'45'scratch'45'zero_274 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'scratch'45'zero_1588
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.st-c-branch-tag-zero
d_st'45'c'45'branch'45'tag'45'zero_276 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'branch'45'tag'45'zero_276 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'tag'45'zero_1606
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.st-c-jmp
d_st'45'c'45'jmp_278 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'jmp_278 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'jmp_1572
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.st-load-indirect
d_st'45'load'45'indirect_280 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'load'45'indirect_280 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect_1540
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.st-load-indirect-suc
d_st'45'load'45'indirect'45'suc_282 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'load'45'indirect'45'suc_282 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect'45'suc_1556
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-guard
d_store'45'guard_284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'guard_284 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.stuck-result
d_stuck'45'result_286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuck'45'result_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_stuck'45'result_286 v20
du_stuck'45'result_286 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuck'45'result_286 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-alloc-heap
d_bs'45'alloc'45'heap_290 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'alloc'45'heap_290 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2046
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-branch-nz
d_bs'45'c'45'branch'45'nz_292 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'nz_292 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1856
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-branch-scratch-zero
d_bs'45'c'45'branch'45'scratch'45'zero_294 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'scratch'45'zero_294 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1842
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-branch-tag-nz
d_bs'45'c'45'branch'45'tag'45'nz_296 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'nz_296 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1890
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-branch-tag-zero
d_bs'45'c'45'branch'45'tag'45'zero_298 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'zero_298 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1874
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-jmp
d_bs'45'c'45'jmp_300 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'jmp_300 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1826
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-label
d_bs'45'c'45'label_302 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'label_302 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1556
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-ret
d_bs'45'c'45'ret_304 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [Integer] ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'ret_304 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_1962
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-c-thunk
d_bs'45'c'45'thunk_306 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'thunk_306 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1940
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-call
d_bs'45'call_308 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'call_308 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2022
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-count-inc
d_bs'45'count'45'inc_310 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'inc_310 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1914
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-count-zero
d_bs'45'count'45'zero_312 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'zero_312 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1534
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-lea-slot
d_bs'45'lea'45'slot_314 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'lea'45'slot_314 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1604
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-code-addr
d_bs'45'load'45'code'45'addr_316 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'code'45'addr_316 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2000
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-const
d_bs'45'load'45'const_318 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const_318 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_1974
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-const-float
d_bs'45'load'45'const'45'float_320 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const'45'float_320 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_1986
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-from-slot
d_bs'45'load'45'from'45'slot_322 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'from'45'slot_322 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1700
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-indirect
d_bs'45'load'45'indirect_324 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect_324 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1640
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-indirect-stack
d_bs'45'load'45'indirect'45'stack_326 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'stack_326 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1656
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-indirect-suc
d_bs'45'load'45'indirect'45'suc_328 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc_328 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1670
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-indirect-suc-stack
d_bs'45'load'45'indirect'45'suc'45'stack_330 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc'45'stack_330 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1686
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-load-tag-lit
d_bs'45'load'45'tag'45'lit_332 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'tag'45'lit_332 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1626
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-mov-input2-to-output
d_bs'45'mov'45'input2'45'to'45'output_334 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'input2'45'to'45'output_334 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'input2'45'to'45'output_1494
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-mov-output-to-input2
d_bs'45'mov'45'output'45'to'45'input2_336 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'output'45'to'45'input2_336 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'output'45'to'45'input2_1504
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-mov-to-input
d_bs'45'mov'45'to'45'input_338 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'input_338 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1484
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-mov-to-output
d_bs'45'mov'45'to'45'output_340 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'output_340 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1474
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-reclaim-to
d_bs'45'reclaim'45'to_342 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'reclaim'45'to_342 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1568
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-restore-input
d_bs'45'restore'45'input_344 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'restore'45'input_344 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1714
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-save-closure-reg
d_bs'45'save'45'closure'45'reg_346 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'save'45'closure'45'reg_346 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1614
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-scratch-dec
d_bs'45'scratch'45'dec_348 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'dec_348 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1902
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-scratch-load-count
d_bs'45'scratch'45'load'45'count_350 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'load'45'count_350 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-scratch-one
d_bs'45'scratch'45'one_352 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'one_352 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-scratch-zero
d_bs'45'scratch'45'zero_354 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'zero_354 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1524
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-store-at-slot
d_bs'45'store'45'at'45'slot_356 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'at'45'slot_356 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-store-indirect
d_bs'45'store'45'indirect_358 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect_358 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1768
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-store-indirect-stack
d_bs'45'store'45'indirect'45'stack_360 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'stack_360 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1784
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-store-indirect-suc
d_bs'45'store'45'indirect'45'suc_362 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'suc_362 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1796
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-store-indirect-suc-stack
d_bs'45'store'45'indirect'45'suc'45'stack_364 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'suc'45'stack_364 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1812
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-worklist-check
d_bs'45'worklist'45'check_366 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'check_366 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1592
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-worklist-init
d_bs'45'worklist'45'init_368 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'init_368 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1580
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-worklist-pop
d_bs'45'worklist'45'pop_370 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'pop_370 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1728
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.BlockSteps.bs-worklist-push
d_bs'45'worklist'45'push_372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'push_372 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1756
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.+-not-<
d_'43''45'not'45''60'_376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_376 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.AddrMap
d_AddrMap_378 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ExtDom
d_ExtDom_382 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr
d_FlatCorr_384 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.GapNext
d_GapNext_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_GapNext_388 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HDom
d_HDom_390 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_390 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView
d_HeapView_392 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Memory
d_Memory_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Memory_396 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.RetAddrs
d_RetAddrs_398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer] -> ()
d_RetAddrs_398 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Sets2Roles
d_Sets2Roles_400 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                 a15 a16
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsMem
d_SetsMem_404 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRole
d_SetsRole_408 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRoleMem
d_SetsRoleMem_412 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                  a15 a16
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.StackWindows
d_StackWindows_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_416 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Window
d_Window_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny -> Integer -> ()
d_Window_418 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Word
d_Word_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Word_420 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.amap
d_amap_422 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422
d_amap_422 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkAddrMap_432
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_390
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_396
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.at-addr
d_at'45'addr_424 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_424 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.at-role
d_at'45'role_426 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_426 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.at-role₁
d_at'45'role'8321'_428 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_428 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.at-role₂
d_at'45'role'8322'_430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_430 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.atstack-frame-inj
d_atstack'45'frame'45'inj_432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_432 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.atstack-slot-inj
d_atstack'45'slot'45'inj_434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_434 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.caddr
d_caddr_436 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_436 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_396
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.clos-eq
d_clos'45'eq_438 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_438 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.cmap
d_cmap_440 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_440 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_cmap_430
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.corr-regs-agree
d_corr'45'regs'45'agree_442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_corr'45'regs'45'agree_442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_corr'45'regs'45'agree_442
du_corr'45'regs'45'agree_442 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_corr'45'regs'45'agree_442 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_corr'45'regs'45'agree_4768
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.corr-store-gap
d_corr'45'store'45'gap_444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_corr'45'store'45'gap_444 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_corr'45'store'45'gap_444 v1 v2
du_corr'45'store'45'gap_444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_corr'45'store'45'gap_444 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_corr'45'store'45'gap_4816
      (coe v0) (coe v1) v3 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.count-eq
d_count'45'eq_446 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_446 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.dec-enc
d_dec'45'enc_448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_448 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.descend-view
d_descend'45'view_450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362
d_descend'45'view_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_descend'45'view_450
du_descend'45'view_450 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362
du_descend'45'view_450 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1538
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.dom-below
d_dom'45'below_452 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_452 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_410
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.dom-fresh
d_dom'45'fresh_454 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_454 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'fresh_1054
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.dom-sized
d_dom'45'sized_456 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_456 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1064
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.dom-written
d_dom'45'written_458 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_458 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1060
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-ext
d_enc'45'ext_460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_460 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-ext-maybe
d_enc'45'ext'45'maybe_462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_462 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-maybe
d_enc'45'maybe_464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_464 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enc'45'maybe_464 v1
du_enc'45'maybe_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_464 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'maybe_478
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-maybe-at
d_enc'45'maybe'45'at_466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_466 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_enc'45'maybe'45'at_466 v1
du_enc'45'maybe'45'at_466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_466 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'maybe'45'at_462
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-sv
d_enc'45'sv_468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_468 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enc'45'sv_468 v1
du_enc'45'sv_468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_468 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'sv_474
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-sv-at
d_enc'45'sv'45'at_470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_470 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enc'45'sv'45'at_470 v1
du_enc'45'sv'45'at_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_470 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'sv'45'at_434
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.enc-zero
d_enc'45'zero_472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_472 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-addr
d_ext'45'addr_474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_474 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ext'45'addr_474 v2
du_ext'45'addr_474 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_474 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ext'45'addr_3862
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-addr-aux
d_ext'45'addr'45'aux_476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_476 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_ext'45'addr'45'aux_476 v2
du_ext'45'addr'45'aux_476 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_476 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ext'45'addr'45'aux_3844
      (coe v0) v1 v2 v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-addr-base
d_ext'45'addr'45'base_478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_478 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-addr-fresh
d_ext'45'addr'45'fresh_480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_480 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-addr-old
d_ext'45'addr'45'old_482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_482 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-suc
d_ext'45'suc_488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_488 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ext-suc-aux
d_ext'45'suc'45'aux_490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_490 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.extend-view
d_extend'45'view_492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362
d_extend'45'view_492 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_extend'45'view_492 v2
du_extend'45'view_492 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362
du_extend'45'view_492 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_extend'45'view_4020
      (coe v0) v1 v2 v3 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.frames-of
d_frames'45'of_494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_frames'45'of_494
du_frames'45'of_494 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_494
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_frames'45'of_482
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.front-lo
d_front'45'lo_496 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_496 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_414
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.frontier-eq
d_frontier'45'eq_498 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_498 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.haddr
d_haddr_500 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_500 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_390
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.haddr-inj
d_haddr'45'inj_502 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_502 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.haddr-suc
d_haddr'45'suc_504 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_504 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.halt-eq
d_halt'45'eq_506 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_506 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.heap-eq
d_heap'45'eq_508 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_508 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.hfront
d_hfront_510 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer
d_hfront_510 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_394
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.hmap
d_hmap_512 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_512 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hmap_428
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.in1-eq
d_in1'45'eq_514 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_514 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.in2-eq
d_in2'45'eq_516 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in2'45'eq_516 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.inc-enc
d_inc'45'enc_518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_518 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-clos
d_keep'45'clos_520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'clos_520 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-count
d_keep'45'count_522 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'count_522 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-halt
d_keep'45'halt_524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'halt_524 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-heap
d_keep'45'heap_526 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap_526 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-heap-reg
d_keep'45'heap'45'reg_528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap'45'reg_528 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-in1
d_keep'45'in1_530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in1_530 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-in2
d_keep'45'in2_532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in2_532 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-lo-le
d_keep'45'lo'45'le_534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_keep'45'lo'45'le_534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_keep'45'lo'45'le_534
du_keep'45'lo'45'le_534 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_keep'45'lo'45'le_534 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_keep'45'lo'45'le_1184
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-out
d_keep'45'out_536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'out_536 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-scratch
d_keep'45'scratch_538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'scratch_538 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-sp
d_keep'45'sp_540 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'sp_540 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-stack
d_keep'45'stack_542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_keep'45'stack_542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_keep'45'stack_542
du_keep'45'stack_542 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_keep'45'stack_542 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_keep'45'stack_1202
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keep-untouched
d_keep'45'untouched_544 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'untouched_544 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keeps-halt
d_keeps'45'halt_546 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_546 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keeps-halt₂
d_keeps'45'halt'8322'_548 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_548 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keeps-mem
d_keeps'45'mem_550 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_550 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.keeps-mem₂
d_keeps'45'mem'8322'_552 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_552 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.lit-word
d_lit'45'word_554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_lit'45'word_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_lit'45'word_554 v11
du_lit'45'word_554 :: Integer -> Integer
du_lit'45'word_554 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.lo
d_lo_556 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer
d_lo_556 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.lo-le
d_lo'45'le_558 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_558 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo'45'le_1070
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mem-halt
d_mem'45'halt_560 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_560 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mem-regs
d_mem'45'regs_562 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_562 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-clos
d_mkeep'45'clos_568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'clos_568 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-count
d_mkeep'45'count_570 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'count_570 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-halt
d_mkeep'45'halt_572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'halt_572 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-heap-reg
d_mkeep'45'heap'45'reg_574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'heap'45'reg_574 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-in1
d_mkeep'45'in1_576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in1_576 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-in2
d_mkeep'45'in2_578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in2_578 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-lo-le
d_mkeep'45'lo'45'le_580 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mkeep'45'lo'45'le_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_mkeep'45'lo'45'le_580
du_mkeep'45'lo'45'le_580 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mkeep'45'lo'45'le_580 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_mkeep'45'lo'45'le_1288
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-out
d_mkeep'45'out_582 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'out_582 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-scratch
d_mkeep'45'scratch_584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'scratch_584 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.mkeep-sp
d_mkeep'45'sp_586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'sp_586 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.nz⇒pos
d_nz'8658'pos_588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nz'8658'pos_588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_nz'8658'pos_588
du_nz'8658'pos_588 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nz'8658'pos_588 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_nz'8658'pos_60
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.off-addr
d_off'45'addr_590 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_590 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.off-role
d_off'45'role_592 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_592 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.off-roles
d_off'45'roles_594 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_594 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.out-eq
d_out'45'eq_596 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_596 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.read-write-hit
d_read'45'write'45'hit_598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'hit_598 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.read-write-miss
d_read'45'write'45'miss_600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_600 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.readMem
d_readMem_602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_readMem_602
du_readMem_602 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
du_readMem_602
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_readMem_68
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-agree-above
d_ret'45'agree'45'above_604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'above_604 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_ret'45'agree'45'above_604 v1 v2
du_ret'45'agree'45'above_604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'above_604 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'agree'45'above_4896
      (coe v0) (coe v1) v2 v8 v11 v12 v14 v15 v16
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-agree-nothing
d_ret'45'agree'45'nothing_606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'nothing_606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_ret'45'agree'45'nothing_606
du_ret'45'agree'45'nothing_606 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'nothing_606 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'agree'45'nothing_5252
      v8 v9 v11 v12
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-head
d_ret'45'head_608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_ret'45'head_608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'head_608
du_ret'45'head_608 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
du_ret'45'head_608 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'head_888
      v3 v9 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-nil-frames
d_ret'45'nil'45'frames_610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
d_ret'45'nil'45'frames_610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_ret'45'nil'45'frames_610
du_ret'45'nil'45'frames_610 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
du_ret'45'nil'45'frames_610 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'nil'45'frames_5352
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-relink
d_ret'45'relink_612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_ret'45'relink_612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'relink_612
du_ret'45'relink_612 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_ret'45'relink_612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'relink_696
      v0 v3 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-relk
d_ret'45'relk_614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ret'45'relk_614 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'relk_614 v1 v2
du_ret'45'relk_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ret'45'relk_614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'relk_782
      (coe v0) (coe v1) v2 v6 v7 v8 v9 v10
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-spill
d_ret'45'spill_616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  AgdaAny ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_ret'45'spill_616 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'spill_616 v1
du_ret'45'spill_616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  AgdaAny ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_ret'45'spill_616 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'spill_5406
      (coe v0) v11 v12 v13 v15
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-unlink
d_ret'45'unlink_618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_ret'45'unlink_618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'unlink_618
du_ret'45'unlink_618 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_ret'45'unlink_618 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'unlink_610
      v0 v3 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.ret-write-in-frame
d_ret'45'write'45'in'45'frame_620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_ret'45'write'45'in'45'frame_620 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                  ~v9 ~v10
  = du_ret'45'write'45'in'45'frame_620 v1 v2
du_ret'45'write'45'in'45'frame_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_ret'45'write'45'in'45'frame_620 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'write'45'in'45'frame_5082
      (coe v0) (coe v1) v2 v7 v9 v12 v13 v14 v15 v16 v17 v18 v19
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.rm-at-addr
d_rm'45'at'45'addr_622 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_622 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.rm-at-role
d_rm'45'at'45'role_624 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_624 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.rm-halt
d_rm'45'halt_626 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_626 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.rm-off-addr
d_rm'45'off'45'addr_628 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_628 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.rm-off-role
d_rm'45'off'45'role_630 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_630 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.scratch-eq
d_scratch'45'eq_632 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_632 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sep
d_sep_634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 = du_sep_634
du_sep_634 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_634 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sep_1528
      v0 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-alloc-heap
d_sim'45'alloc'45'heap_636 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'alloc'45'heap_636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_sim'45'alloc'45'heap_636
du_sim'45'alloc'45'heap_636 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'alloc'45'heap_636 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'alloc'45'heap_4360
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-alloc-stack
d_sim'45'alloc'45'stack_638 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'alloc'45'stack_638 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_sim'45'alloc'45'stack_638 v1 v2
du_sim'45'alloc'45'stack_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'alloc'45'stack_638 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'alloc'45'stack_3242
      (coe v0) (coe v1) v3 v4 v7 v12
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-call-frame
d_sim'45'call'45'frame_640 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'call'45'frame_640 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10
  = du_sim'45'call'45'frame_640 v1 v2 v6 v9
du_sim'45'call'45'frame_640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'call'45'frame_640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'call'45'frame_3476
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
         (coe v3))
      v6 v7 v9 v13
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-dealloc-stack
d_sim'45'dealloc'45'stack_642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'dealloc'45'stack_642 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
                              ~v10
  = du_sim'45'dealloc'45'stack_642 v1 v6 v9
du_sim'45'dealloc'45'stack_642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'dealloc'45'stack_642 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'dealloc'45'stack_3560
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
         (coe v2))
      v5 v6 v8
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-lea-slot
d_sim'45'lea'45'slot_644 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'lea'45'slot_644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_sim'45'lea'45'slot_644
du_sim'45'lea'45'slot_644 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'lea'45'slot_644 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'lea'45'slot_4490
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-code-addr
d_sim'45'load'45'code'45'addr_646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'code'45'addr_646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_sim'45'load'45'code'45'addr_646
du_sim'45'load'45'code'45'addr_646 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'code'45'addr_646 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'code'45'addr_3716
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-const
d_sim'45'load'45'const_648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'const_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_sim'45'load'45'const_648
du_sim'45'load'45'const_648 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'const_648 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'const_3662
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-const-float
d_sim'45'load'45'const'45'float_650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'const'45'float_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10
  = du_sim'45'load'45'const'45'float_650
du_sim'45'load'45'const'45'float_650 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'const'45'float_650 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'const'45'float_3688
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-from-slot
d_sim'45'load'45'from'45'slot_652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'from'45'slot_652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_sim'45'load'45'from'45'slot_652
du_sim'45'load'45'from'45'slot_652 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'from'45'slot_652 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'from'45'slot_1914
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-indirect
d_sim'45'load'45'indirect_654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'indirect_654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_sim'45'load'45'indirect_654
du_sim'45'load'45'indirect_654 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'indirect_654 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect_1860
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_656 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'indirect'45'stack_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'stack_656
du_sim'45'load'45'indirect'45'stack_656 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'indirect'45'stack_656 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_4532
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'indirect'45'suc_658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'suc_658
du_sim'45'load'45'indirect'45'suc_658 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'indirect'45'suc_658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_1806
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'indirect'45'suc'45'stack_660 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'suc'45'stack_660
du_sim'45'load'45'indirect'45'suc'45'stack_660 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'indirect'45'suc'45'stack_660 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_4590
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'load'45'tag'45'lit_662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_sim'45'load'45'tag'45'lit_662
du_sim'45'load'45'tag'45'lit_662 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'load'45'tag'45'lit_662 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_1676
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_664 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'mov'45'input2'45'to'45'output_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'mov'45'input2'45'to'45'output_664
du_sim'45'mov'45'input2'45'to'45'output_664 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'mov'45'input2'45'to'45'output_664 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'input2'45'to'45'output_1630
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'mov'45'output'45'to'45'input2_666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'mov'45'output'45'to'45'input2_666
du_sim'45'mov'45'output'45'to'45'input2_666 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'mov'45'output'45'to'45'input2_666 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'output'45'to'45'input2_1652
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-mov-to-input
d_sim'45'mov'45'to'45'input_668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'mov'45'to'45'input_668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_sim'45'mov'45'to'45'input_668
du_sim'45'mov'45'to'45'input_668 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'mov'45'to'45'input_668 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'to'45'input_1608
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-mov-to-output
d_sim'45'mov'45'to'45'output_670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'mov'45'to'45'output_670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_sim'45'mov'45'to'45'output_670
du_sim'45'mov'45'to'45'output_670 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'mov'45'to'45'output_670 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'to'45'output_1586
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_672 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'reg'45'count'45'inc_672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_sim'45'reg'45'count'45'inc_672
du_sim'45'reg'45'count'45'inc_672 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'reg'45'count'45'inc_672 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_3788
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_674 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'reg'45'count'45'zero_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_sim'45'reg'45'count'45'zero_674
du_sim'45'reg'45'count'45'zero_674 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'reg'45'count'45'zero_674 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_1744
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'reg'45'scratch'45'dec_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'dec_676
du_sim'45'reg'45'scratch'45'dec_676 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'reg'45'scratch'45'dec_676 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_3818
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'reg'45'scratch'45'load'45'count_678 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'load'45'count_678
du_sim'45'reg'45'scratch'45'load'45'count_678 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'reg'45'scratch'45'load'45'count_678 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_1766
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'reg'45'scratch'45'one_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'one_680
du_sim'45'reg'45'scratch'45'one_680 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'reg'45'scratch'45'one_680 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_1700
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'reg'45'scratch'45'zero_682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'zero_682
du_sim'45'reg'45'scratch'45'zero_682 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'reg'45'scratch'45'zero_682 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_1722
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-restore-input
d_sim'45'restore'45'input_684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'restore'45'input_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_sim'45'restore'45'input_684
du_sim'45'restore'45'input_684 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'restore'45'input_684 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'restore'45'input_2896
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-ret
d_sim'45'ret_686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'ret_686 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10
  = du_sim'45'ret_686 v1 v2 v6 v9
du_sim'45'ret_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'ret_686 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'ret_3608
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
         (coe v3))
      v5 v8 v9 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'save'45'closure'45'reg_688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10
  = du_sim'45'save'45'closure'45'reg_688
du_sim'45'save'45'closure'45'reg_688 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'save'45'closure'45'reg_688 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'save'45'closure'45'reg_3744
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-store-at-slot
d_sim'45'store'45'at'45'slot_690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'store'45'at'45'slot_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_sim'45'store'45'at'45'slot_690
du_sim'45'store'45'at'45'slot_690 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'store'45'at'45'slot_690 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'at'45'slot_3188
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-store-indirect
d_sim'45'store'45'indirect_692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'store'45'indirect_692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_sim'45'store'45'indirect_692
du_sim'45'store'45'indirect_692 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'store'45'indirect_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect_2790
      v1 v2 v5 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'store'45'indirect'45'stack_694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'stack_694
du_sim'45'store'45'indirect'45'stack_694 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'store'45'indirect'45'stack_694 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_4646
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'store'45'indirect'45'suc_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'suc_696
du_sim'45'store'45'indirect'45'suc_696 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'store'45'indirect'45'suc_696 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_2842
      v1 v2 v5 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'store'45'indirect'45'suc'45'stack_698 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'suc'45'stack_698
du_sim'45'store'45'indirect'45'suc'45'stack_698 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'store'45'indirect'45'suc'45'stack_698 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_4708
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sim-thunk
d_sim'45'thunk_700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_sim'45'thunk_700 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'thunk_700 v1 v2
du_sim'45'thunk_700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_sim'45'thunk_700 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'thunk_3344
      (coe v0) (coe v1) v3 v4 v7 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.slot-addr-inj
d_slot'45'addr'45'inj_702 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_702 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.slot-size>0
d_slot'45'size'62'0_704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'size'62'0_704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_slot'45'size'62'0_704
du_slot'45'size'62'0_704 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'size'62'0_704
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slot'45'size'62'0_62
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.slot-to-disp
d_slot'45'to'45'disp_706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_slot'45'to'45'disp_706 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_slot'45'to'45'disp_706 v2
du_slot'45'to'45'disp_706 :: Integer -> Integer -> Integer
du_slot'45'to'45'disp_706 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slot'45'to'45'disp_54
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.slots
d_slots_708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_slots_708 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_slots_708 v2
du_slots_708 :: Integer -> Integer -> Integer
du_slots_708 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_50
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sp-eq
d_sp'45'eq_710 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_710 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.stack-eq
d_stack'45'eq_712 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_712 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_stack'45'eq_1076
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.stack-eq-cur
d_stack'45'eq'45'cur_714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_714 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.stack-eq-win
d_stack'45'eq'45'win_716 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_716 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.store-dom-written
d_store'45'dom'45'written_718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_store'45'dom'45'written_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_store'45'dom'45'written_718
du_store'45'dom'45'written_718 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_718 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_store'45'dom'45'written_2190
      v1 v4 v5 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.store-heap-eq
d_store'45'heap'45'eq_720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_720 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_722 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_722 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_724 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.sv-tag-zero
d_sv'45'tag'45'zero_726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_726 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.untouched
d_untouched_728 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_728 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.untouched-descend
d_untouched'45'descend_730 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_730 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.untouched-heap-store
d_untouched'45'heap'45'store_732 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_732 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.untouched-stack-store
d_untouched'45'stack'45'store_734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_734 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.untouched-write
d_untouched'45'write_736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_736 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.win-at
d_win'45'at_738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_738 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.win-off
d_win'45'off_740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_740 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.window-store-above
d_window'45'store'45'above_742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_window'45'store'45'above_742 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-above
d_windows'45'above_744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'above_744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_windows'45'above_744
du_windows'45'above_744 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'above_744 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'above_2500
      v6 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-enc-ext
d_windows'45'enc'45'ext_746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_windows'45'enc'45'ext_746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_windows'45'enc'45'ext_746
du_windows'45'enc'45'ext_746 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_746 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'enc'45'ext_4278
      v8 v10
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-forget
d_windows'45'forget_748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'forget_748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_windows'45'forget_748
du_windows'45'forget_748 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'forget_748 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'forget_2380
      v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-heap-store
d_windows'45'heap'45'store_750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_windows'45'heap'45'store_750
du_windows'45'heap'45'store_750 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_750 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'heap'45'store_2762
      v1 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-leave
d_windows'45'leave_752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_752 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_windows'45'leave_752 v1
du_windows'45'leave_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_752 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'leave_2434
      (coe v0) v4 v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-lower
d_windows'45'lower_754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'lower_754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_windows'45'lower_754
du_windows'45'lower_754 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'lower_754 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'lower_2334
      v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-reanchor
d_windows'45'reanchor_756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'reanchor_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10
  = du_windows'45'reanchor_756
du_windows'45'reanchor_756 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_756 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'reanchor_2304
      v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-slot-store
d_windows'45'slot'45'store_758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_windows'45'slot'45'store_758
du_windows'45'slot'45'store_758 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'slot'45'store_3116
      v9 v12
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-store-gap
d_windows'45'store'45'gap_760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'store'45'gap_760 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                              ~v10
  = du_windows'45'store'45'gap_760 v1 v2
du_windows'45'store'45'gap_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'store'45'gap_760 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'store'45'gap_2624
      (coe v0) (coe v1) v7 v8 v9 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.windows-write-below
d_windows'45'write'45'below_762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_windows'45'write'45'below_762
du_windows'45'write'45'below_762 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_762 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'write'45'below_2714
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.writeMem
d_writeMem_764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_writeMem_764
du_writeMem_764 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
du_writeMem_764
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_writeMem_74
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.≡ᵇ-refl
d_'8801''7495''45'refl_766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_766 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_768 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.AddrMap.cmap
d_cmap_772 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_772 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_cmap_430
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.AddrMap.hmap
d_hmap_774 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_422 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_774 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hmap_428
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.clos-eq
d_clos'45'eq_784 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_784 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.count-eq
d_count'45'eq_786 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_786 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.dom-fresh
d_dom'45'fresh_788 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_788 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'fresh_1054
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.dom-sized
d_dom'45'sized_790 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_790 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1064
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.dom-written
d_dom'45'written_792 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_792 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1060
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.frontier-eq
d_frontier'45'eq_794 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_794 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.halt-eq
d_halt'45'eq_796 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_796 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.heap-eq
d_heap'45'eq_798 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_798 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.in1-eq
d_in1'45'eq_800 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_800 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.in2-eq
d_in2'45'eq_802 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in2'45'eq_802 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.lo-le
d_lo'45'le_804 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_804 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo'45'le_1070
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.out-eq
d_out'45'eq_806 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_806 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.scratch-eq
d_scratch'45'eq_808 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_808 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.sp-eq
d_sp'45'eq_810 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_810 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.stack-eq
d_stack'45'eq_812 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_812 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_stack'45'eq_1076
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.FlatCorr.untouched
d_untouched_814 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_814 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.HDom
d_HDom_818 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_818 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.caddr
d_caddr_820 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_820 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_396
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.dom-below
d_dom'45'below_822 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_822 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_410
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.front-lo
d_front'45'lo_824 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_824 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_414
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr
d_haddr_826 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_826 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_390
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr-inj
d_haddr'45'inj_828 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_828 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.haddr-suc
d_haddr'45'suc_830 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_830 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.hfront
d_hfront_832 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer
d_hfront_832 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_394
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.HeapView.lo
d_lo_834 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer
d_lo_834 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Sets2Roles.at-role₁
d_at'45'role'8321'_838 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_838 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Sets2Roles.at-role₂
d_at'45'role'8322'_840 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_840 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Sets2Roles.keeps-halt₂
d_keeps'45'halt'8322'_842 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_842 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Sets2Roles.keeps-mem₂
d_keeps'45'mem'8322'_844 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_844 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.Sets2Roles.off-roles
d_off'45'roles_846 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_846 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsMem.at-addr
d_at'45'addr_850 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_850 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsMem.mem-halt
d_mem'45'halt_852 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_852 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsMem.mem-regs
d_mem'45'regs_854 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_854 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsMem.off-addr
d_off'45'addr_856 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1214 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_856 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRole.at-role
d_at'45'role_860 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_860 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRole.keeps-halt
d_keeps'45'halt_862 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_862 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRole.keeps-mem
d_keeps'45'mem_864 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_864 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRole.off-role
d_off'45'role_866 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_866 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRoleMem.rm-at-addr
d_rm'45'at'45'addr_870 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_870 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRoleMem.rm-at-role
d_rm'45'at'45'role_872 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_872 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRoleMem.rm-halt
d_rm'45'halt_874 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_874 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRoleMem.rm-off-addr
d_rm'45'off'45'addr_876 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_876 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CFC.SetsRoleMem.rm-off-role
d_rm'45'off'45'role_878 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1304 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_878 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.code-eq
d_code'45'eq_882 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_882 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.dataCorr
d_dataCorr_884 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_dataCorr_884 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.pc-off
d_pc'45'off_886 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_886 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.CompiledCorr.ret-eq
d_ret'45'eq_888 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  AgdaAny
d_ret'45'eq_888 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_694
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-closure
d_inv'45'closure_892 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  AgdaAny
d_inv'45'closure_892 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1074
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-env
d_inv'45'env_894 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'env_894 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-ev
d_inv'45'ev_896 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_896 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-regtag
d_inv'45'regtag_898 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_394
d_inv'45'regtag_898 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'regtag_1076
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-run
d_inv'45'run_900 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288
d_inv'45'run_900 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.FlatInv.inv-wf
d_inv'45'wf_902 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586
d_inv'45'wf_902 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.ArithEnv
d_ArithEnv_906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_ArithEnv_906 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.EvExtractor
d_EvExtractor_908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_EvExtractor_908 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events
d_run'45'events_910 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events_910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_run'45'events_910 v8 v9 v10
du_run'45'events_910 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_run'45'events_910 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events_36
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-[]
d_run'45'events'45''91''93'_912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  (Integer ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_912 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-arith
d_run'45'events'45'arith_914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'arith_914 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-call
d_run'45'events'45'call_916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'call_916 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                            v10
  = du_run'45'events'45'call_916 v8 v9 v10
du_run'45'events'45'call_916 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_run'45'events'45'call_916 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'call_42
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-exec
d_run'45'events'45'exec_918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'exec_918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                            v10
  = du_run'45'events'45'exec_918 v8 v9 v10
du_run'45'events'45'exec_918 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_run'45'events'45'exec_918 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'exec_44
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
      v3 v4 v5 v6 v8
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-external
d_run'45'events'45'external_920 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'external_920 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-fetch
d_run'45'events'45'fetch_922 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'fetch_922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                             v10
  = du_run'45'events'45'fetch_922 v8 v9 v10
du_run'45'events'45'fetch_922 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_run'45'events'45'fetch_922 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'fetch_38
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-fetch-none
d_run'45'events'45'fetch'45'none_924 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_924 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-halted
d_run'45'events'45'halted_926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_926 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-instr
d_run'45'events'45'instr_928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'events'45'instr_928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                             v10
  = du_run'45'events'45'instr_928 v8 v9 v10
du_run'45'events'45'instr_928 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_run'45'events'45'instr_928 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'events'45'instr_40
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-noncall
d_run'45'events'45'noncall_930 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'noncall_930 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-events-stuck
d_run'45'events'45'stuck_932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_932 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RT.run-trace
d_run'45'trace_934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_run'45'trace_934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_run'45'trace_934 v8 v9 v10
du_run'45'trace_934 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_run'45'trace_934 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_162
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-emit
d_run'45'emit_944 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_944 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-heap
d_run'45'heap_946 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  AgdaAny
d_run'45'heap_946 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'heap_306
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-ir
d_run'45'ir_948 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_948 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_302
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RunAt.run-reach
d_run'45'reach_950 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_262
d_run'45'reach_950 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_308
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckSteps.st-c-branch-scratch-zero
d_st'45'c'45'branch'45'scratch'45'zero_954 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'branch'45'scratch'45'zero_954 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'scratch'45'zero_1588
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckSteps.st-c-branch-tag-zero
d_st'45'c'45'branch'45'tag'45'zero_956 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'branch'45'tag'45'zero_956 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'tag'45'zero_1606
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckSteps.st-c-jmp
d_st'45'c'45'jmp_958 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'jmp_958 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'jmp_1572
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckSteps.st-load-indirect
d_st'45'load'45'indirect_960 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'load'45'indirect_960 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect_1540
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.StuckSteps.st-load-indirect-suc
d_st'45'load'45'indirect'45'suc_962 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'load'45'indirect'45'suc_962 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect'45'suc_1556
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.arith-sigop-contract
d_arith'45'sigop'45'contract_966 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arith'45'sigop'45'contract_966 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_arith'45'sigop'45'contract_1972
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.bss
d_bss_968 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_882
d_bss_968 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.call-room
d_call'45'room_970 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_call'45'room_970 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1862
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.count-no-wrap
d_count'45'no'45'wrap_972 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_972 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_count'45'no'45'wrap_1906
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.external-sigop-contract
d_external'45'sigop'45'contract_974 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_external'45'sigop'45'contract_974 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_external'45'sigop'45'contract_1992
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.float-fits
d_float'45'fits_976 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_976 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_float'45'fits_1942
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.heap-room
d_heap'45'room_978 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'room_978 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1838
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.lit-fits
d_lit'45'fits_980 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_980 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lit'45'fits_1930
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.lo-fits
d_lo'45'fits_982 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_982 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lo'45'fits_1952
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.reg-range
d_reg'45'range_984 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reg'45'range_984 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1874
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.ret-no-wrap
d_ret'45'no'45'wrap_986 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_986 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_ret'45'no'45'wrap_1896
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.scratch-dec-guarded
d_scratch'45'dec'45'guarded_988 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'dec'45'guarded_988 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_scratch'45'dec'45'guarded_1884
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.stack-room
d_stack'45'room_990 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'room_990 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1852
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.sts
d_sts_992 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_StuckSteps_1442
d_sts_992 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1826
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Supply.tag-fits
d_tag'45'fits_994 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_994 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_tag'45'fits_1918
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.compile-trace
d_compile'45'trace_1002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [AgdaAny]
d_compile'45'trace_1002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_compile'45'trace_1002 v8
du_compile'45'trace_1002 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  [AgdaAny]
du_compile'45'trace_1002 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'trace_108
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.memory
d_memory_1056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> Integer -> Maybe Integer
d_memory_1056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_memory_1056 v9
du_memory_1056 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> Integer -> Maybe Integer
du_memory_1056 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_memory_290
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.rreg
d_rreg_1060 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> AgdaAny -> Integer
d_rreg_1060 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_rreg_1060 v9
du_rreg_1060 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> AgdaAny -> Integer
du_rreg_1060 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.in1-reg
d_in1'45'reg_1092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_in1'45'reg_1092 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_in1'45'reg_1092 v6
du_in1'45'reg_1092 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_in1'45'reg_1092 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_46
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.sp-reg
d_sp'45'reg_1096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_sp'45'reg_1096 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_sp'45'reg_1096 v6
du_sp'45'reg_1096 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_sp'45'reg_1096 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.enter-call
d_enter'45'call_1110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_enter'45'call_1110 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enter'45'call_1110 v1
du_enter'45'call_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_enter'45'call_1110 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_538 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch
d_fetch_1116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
d_fetch_1116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_fetch_1116
du_fetch_1116 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
du_fetch_1116 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-thunk
d_find'45'thunk_1118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_1118 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'thunk_1118 v1
du_find'45'thunk_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'thunk_1118 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_208 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-exec-instr
d_flat'45'exec'45'instr_1120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1120 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_flat'45'exec'45'instr_1120 v1
du_flat'45'exec'45'instr_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1120 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1080
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.find-label
d_find'45'label_1122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_1122 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_find'45'label_1122 v1
du_find'45'label_1122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
du_find'45'label_1122 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.readLoc
d_readLoc_1150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_1150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_readLoc_1150
du_readLoc_1150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_1150
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.ir-stack-budget
d_ir'45'stack'45'budget_1198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_1198 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_ir'45'stack'45'budget_1198 v0
du_ir'45'stack'45'budget_1198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
du_ir'45'stack'45'budget_1198 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'stack'45'budget_750
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.Frame
d_Frame_1204 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Frame_1204 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.JumpPost
d_JumpPost_1208 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.NotJmpI
d_NotJmpI_1210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 -> ()
d_NotJmpI_1210 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.PcView
d_PcView_1212 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.RetMatch
d_RetMatch_1214 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.SegCur
d_SegCur_1216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_SegCur_1216 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.SegWF
d_SegWF_1218 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.branch-tag-scrutinee-wf
d_branch'45'tag'45'scrutinee'45'wf_1222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'tag'45'scrutinee'45'wf_1222 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10
  = du_branch'45'tag'45'scrutinee'45'wf_1222 v0 v1 v2
du_branch'45'tag'45'scrutinee'45'wf_1222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'tag'45'scrutinee'45'wf_1222 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_branch'45'tag'45'scrutinee'45'wf_4072
      (coe v0) (coe v1) (coe v2) v3 v4 v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.call-seg-id
d_call'45'seg'45'id_1224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_call'45'seg'45'id_1224 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.call-site-shape
d_call'45'site'45'shape_1226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'site'45'shape_1226 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_call'45'site'45'shape_1226 v0 v1 v2
du_call'45'site'45'shape_1226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'site'45'shape_1226 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_call'45'site'45'shape_1284
      v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.db-aux
d_db'45'aux_1228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_db'45'aux_1228 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_db'45'aux_1228 v1
du_db'45'aux_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_db'45'aux_1228 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_db'45'aux_1518
      (coe v0) v1 v2 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.dj-aux
d_dj'45'aux_1230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dj'45'aux_1230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_dj'45'aux_1230
du_dj'45'aux_1230 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_dj'45'aux_1230 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_dj'45'aux_1500
      v0
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.emitted-alloc-min
d_emitted'45'alloc'45'min_1232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_emitted'45'alloc'45'min_1232 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_emitted'45'alloc'45'min_1232 v0
du_emitted'45'alloc'45'min_1232 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_emitted'45'alloc'45'min_1232 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_emitted'45'alloc'45'min_3190
      (coe v0) v2 v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.emitted-code-addr-has-body
d_emitted'45'code'45'addr'45'has'45'body_1234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_emitted'45'code'45'addr'45'has'45'body_1234 v0 v1 v2 ~v3 ~v4 ~v5
                                              ~v6 ~v7 ~v8 ~v9 ~v10
  = du_emitted'45'code'45'addr'45'has'45'body_1234 v0 v1 v2
du_emitted'45'code'45'addr'45'has'45'body_1234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_emitted'45'code'45'addr'45'has'45'body_1234 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_emitted'45'code'45'addr'45'has'45'body_1320
      v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.emitted-shape-check
d_emitted'45'shape'45'check_1236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_emitted'45'shape'45'check_1236 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                 ~v9 ~v10
  = du_emitted'45'shape'45'check_1236 v0 v1 v2
du_emitted'45'shape'45'check_1236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_emitted'45'shape'45'check_1236 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_emitted'45'shape'45'check_1334
      v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.emitted-slot-below-budget
d_emitted'45'slot'45'below'45'budget_1238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_emitted'45'slot'45'below'45'budget_1238 v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          ~v6 ~v7 ~v8 ~v9 ~v10
  = du_emitted'45'slot'45'below'45'budget_1238 v0
du_emitted'45'slot'45'below'45'budget_1238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_emitted'45'slot'45'below'45'budget_1238 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_emitted'45'slot'45'below'45'budget_1388
      (coe v0) v1 v2 v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.emitted-thunk-guarded
d_emitted'45'thunk'45'guarded_1240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_emitted'45'thunk'45'guarded_1240 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                   ~v9 ~v10
  = du_emitted'45'thunk'45'guarded_1240 v0 v1 v2
du_emitted'45'thunk'45'guarded_1240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_emitted'45'thunk'45'guarded_1240 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_emitted'45'thunk'45'guarded_1310
      v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.entry-flat-wf
d_entry'45'flat'45'wf_1242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586
d_entry'45'flat'45'wf_1242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_entry'45'flat'45'wf_1242
du_entry'45'flat'45'wf_1242 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586
du_entry'45'flat'45'wf_1242
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'flat'45'wf_2962
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.entry-ptr-bounds
d_entry'45'ptr'45'bounds_1244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440
d_entry'45'ptr'45'bounds_1244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_entry'45'ptr'45'bounds_1244
du_entry'45'ptr'45'bounds_1244 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440
du_entry'45'ptr'45'bounds_1244
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'ptr'45'bounds_2894
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.entry-stack-ptr
d_entry'45'stack'45'ptr_1246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400
d_entry'45'stack'45'ptr_1246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10
  = du_entry'45'stack'45'ptr_1246
du_entry'45'stack'45'ptr_1246 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400
du_entry'45'stack'45'ptr_1246
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_entry'45'stack'45'ptr_2826
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.fetch≡lookup
d_fetch'8801'lookup_1248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'8801'lookup_1248 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.ff→seg-id
d_ff'8594'seg'45'id_1250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ff'8594'seg'45'id_1250 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.frame-op-absurd
d_frame'45'op'45'absurd_1252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_frame'45'op'45'absurd_1252 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_frame'45'op'45'absurd_1252 v0
du_frame'45'op'45'absurd_1252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_frame'45'op'45'absurd_1252 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_frame'45'op'45'absurd_1352
      (coe v0) v2 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.load-indirect-suc-target-ptr
d_load'45'indirect'45'suc'45'target'45'ptr_1260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'ptr_1260 v0 v1 v2 ~v3 ~v4
                                                ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_load'45'indirect'45'suc'45'target'45'ptr_1260 v0 v1 v2
du_load'45'indirect'45'suc'45'target'45'ptr_1260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'ptr_1260 v0 v1 v2 v3 v4 v5
                                                 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'suc'45'target'45'ptr_3922
      (coe v0) (coe v1) (coe v2) v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.load-indirect-suc-target-wf
d_load'45'indirect'45'suc'45'target'45'wf_1262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'target'45'wf_1262 v0 v1 v2 ~v3 ~v4 ~v5
                                               ~v6 ~v7 ~v8 ~v9 ~v10
  = du_load'45'indirect'45'suc'45'target'45'wf_1262 v0 v1 v2
du_load'45'indirect'45'suc'45'target'45'wf_1262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'target'45'wf_1262 v0 v1 v2 v3 v4 v5
                                                v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'suc'45'target'45'wf_4202
      (coe v0) (coe v1) (coe v2) v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.load-indirect-target-ptr
d_load'45'indirect'45'target'45'ptr_1264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'ptr_1264 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8 ~v9 ~v10
  = du_load'45'indirect'45'target'45'ptr_1264 v0 v1 v2
du_load'45'indirect'45'target'45'ptr_1264 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'ptr_1264 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'target'45'ptr_3892
      (coe v0) (coe v1) (coe v2) v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.load-indirect-target-wf
d_load'45'indirect'45'target'45'wf_1266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'target'45'wf_1266 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10
  = du_load'45'indirect'45'target'45'wf_1266 v0 v1 v2
du_load'45'indirect'45'target'45'wf_1266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'target'45'wf_1266 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'target'45'wf_4164
      (coe v0) (coe v1) (coe v2) v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.pcView
d_pcView_1270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_PcView_1562
d_pcView_1270 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_pcView_1270 v1
du_pcView_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_PcView_1562
du_pcView_1270 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_pcView_1594
      (coe v0) v1
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.ptr-bounds-step
d_ptr'45'bounds'45'step_1272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440
d_ptr'45'bounds'45'step_1272 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_ptr'45'bounds'45'step_1272 v0 v1
du_ptr'45'bounds'45'step_1272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_586 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440
du_ptr'45'bounds'45'step_1272 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_ptr'45'bounds'45'step_3206
      (coe v0) (coe v1) v2 v3 v4 v5 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.ret-budget-matches
d_ret'45'budget'45'matches_1284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ret'45'budget'45'matches_1284 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.ret-site-owes
d_ret'45'site'45'owes_1286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ret'45'site'45'owes_1286 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_ret'45'site'45'owes_1286 v0 v1 v2
du_ret'45'site'45'owes_1286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ret'45'site'45'owes_1286 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_ret'45'site'45'owes_1296
      v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-link-at-thunk
d_run'45'link'45'at'45'thunk_1292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'link'45'at'45'thunk_1292 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_run'45'link'45'at'45'thunk_1292 v1
du_run'45'link'45'at'45'thunk_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'link'45'at'45'thunk_1292 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'link'45'at'45'thunk_4246
      (coe v0) v1 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-link-nothing
d_run'45'link'45'nothing_1294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'link'45'nothing_1294 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-link-nothing-aux
d_run'45'link'45'nothing'45'aux_1296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'link'45'nothing'45'aux_1296 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-meets
d_run'45'meets_1298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'meets_1298 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_run'45'meets_1298 v0 v1 v2
du_run'45'meets_1298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'meets_1298 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_run'45'meets_1342
      v0 v1 v2 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-ptr-bounds
d_run'45'ptr'45'bounds_1300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440
d_run'45'ptr'45'bounds_1300 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_run'45'ptr'45'bounds_1300 v0 v1
du_run'45'ptr'45'bounds_1300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.CCC.Machine.FlatPtrBounds.T_PBInv_440
du_run'45'ptr'45'bounds_1300 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'ptr'45'bounds_3808
      (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-seg-wf
d_run'45'seg'45'wf_1302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452
d_run'45'seg'45'wf_1302 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_run'45'seg'45'wf_1302 v0 v1 v2
du_run'45'seg'45'wf_1302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452
du_run'45'seg'45'wf_1302 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'seg'45'wf_1800
      (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-shape-check
d_run'45'shape'45'check_1304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'shape'45'check_1304 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_run'45'shape'45'check_1304 v0 v1 v2
du_run'45'shape'45'check_1304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'shape'45'check_1304 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'shape'45'check_3824
      (coe v0) (coe v1) (coe v2) v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-stack-ptr
d_run'45'stack'45'ptr_1306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400
d_run'45'stack'45'ptr_1306 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_run'45'stack'45'ptr_1306 v1
du_run'45'stack'45'ptr_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400
du_run'45'stack'45'ptr_1306 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'stack'45'ptr_3038
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.run-wf-ptr-bounds
d_run'45'wf'45'ptr'45'bounds_1308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'wf'45'ptr'45'bounds_1308 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                  ~v9 ~v10
  = du_run'45'wf'45'ptr'45'bounds_1308 v0 v1
du_run'45'wf'45'ptr'45'bounds_1308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'wf'45'ptr'45'bounds_1308 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'wf'45'ptr'45'bounds_3764
      (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.seg-cur
d_seg'45'cur_1310 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_seg'45'cur_1310 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'cur_1476
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.seg-entry
d_seg'45'entry_1312 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_seg'45'entry_1312 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'entry_1490
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.seg-stack
d_seg'45'stack_1314 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1412
d_seg'45'stack_1314 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'stack_1478
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.slot-read-in-frame
d_slot'45'read'45'in'45'frame_1316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'read'45'in'45'frame_1316 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10
  = du_slot'45'read'45'in'45'frame_1316 v0
du_slot'45'read'45'in'45'frame_1316 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'read'45'in'45'frame_1316 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3126
      (coe v0) v2 v3 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.slot-read-written
d_slot'45'read'45'written_1318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Codegen.ShapeTable.T_Expect_24 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'read'45'written_1318 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.stack-ptr-current
d_stack'45'ptr'45'current_1320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current_1320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_stack'45'ptr'45'current_1320
du_stack'45'ptr'45'current_1320 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current_1320 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3082
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.stack-ptr-current-suc
d_stack'45'ptr'45'current'45'suc_1322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'ptr'45'current'45'suc_1322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9 ~v10
  = du_stack'45'ptr'45'current'45'suc_1322
du_stack'45'ptr'45'current'45'suc_1322 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'ptr'45'current'45'suc_1322 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3104
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.stack-ptr-step
d_stack'45'ptr'45'step_1324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400
d_stack'45'ptr'45'step_1324 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_stack'45'ptr'45'step_1324 v1
du_stack'45'ptr'45'step_1324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStackPtr.T_SPInv_400
du_stack'45'ptr'45'step_1324 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'step_2394
      (coe v0) v1 v2 v3 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-indirect-inbounds
d_store'45'indirect'45'inbounds_1326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'inbounds_1326 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                     ~v8 ~v9 ~v10
  = du_store'45'indirect'45'inbounds_1326 v0 v1
du_store'45'indirect'45'inbounds_1326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'inbounds_1326 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'inbounds_4122
      (coe v0) (coe v1) v2 v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-indirect-suc-inbounds
d_store'45'indirect'45'suc'45'inbounds_1328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_store'45'indirect'45'suc'45'inbounds_1328 v0 v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7 ~v8 ~v9 ~v10
  = du_store'45'indirect'45'suc'45'inbounds_1328 v0 v1
du_store'45'indirect'45'suc'45'inbounds_1328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_store'45'indirect'45'suc'45'inbounds_1328 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'suc'45'inbounds_4142
      (coe v0) (coe v1) v2 v3 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-indirect-suc-target-ptr
d_store'45'indirect'45'suc'45'target'45'ptr_1330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'target'45'ptr_1330 v0 v1 v2 ~v3 ~v4
                                                 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_store'45'indirect'45'suc'45'target'45'ptr_1330 v0 v1 v2
du_store'45'indirect'45'suc'45'target'45'ptr_1330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'target'45'ptr_1330 v0 v1 v2 v3 v4 v5
                                                  v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'suc'45'target'45'ptr_3982
      (coe v0) (coe v1) (coe v2) v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-indirect-target-ptr
d_store'45'indirect'45'target'45'ptr_1332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'target'45'ptr_1332 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10
  = du_store'45'indirect'45'target'45'ptr_1332 v0 v1 v2
du_store'45'indirect'45'target'45'ptr_1332 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'target'45'ptr_1332 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'target'45'ptr_3952
      (coe v0) (coe v1) (coe v2) v3 v4 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-nonptr-absurd
d_store'45'nonptr'45'absurd_1334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'nonptr'45'absurd_1334 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.store-suc-nonptr-absurd
d_store'45'suc'45'nonptr'45'absurd_1336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_store'45'suc'45'nonptr'45'absurd_1336 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.thunk-entry-empty
d_thunk'45'entry'45'empty_1338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'entry'45'empty_1338 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.thunk-entry-link
d_thunk'45'entry'45'link_1340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'entry'45'link_1340 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                              ~v10
  = du_thunk'45'entry'45'link_1340 v0 v1 v2
du_thunk'45'entry'45'link_1340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'entry'45'link_1340 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_thunk'45'entry'45'link_2348
      (coe v0) (coe v1) (coe v2) v3 v4 v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.thunk-entry-ret
d_thunk'45'entry'45'ret_1342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'entry'45'ret_1342 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_thunk'45'entry'45'ret_1342 v0 v1 v2
du_thunk'45'entry'45'ret_1342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'entry'45'ret_1342 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_thunk'45'entry'45'ret_2374
      (coe v0) (coe v1) (coe v2) v3 v4 v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.SegWF.seg-cur
d_seg'45'cur_1372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_seg'45'cur_1372 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'cur_1476
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.SegWF.seg-entry
d_seg'45'entry_1374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_seg'45'entry_1374 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'entry_1490
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.SegWF.seg-stack
d_seg'45'stack_1376 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_SegWF_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1412
d_seg'45'stack_1376 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'stack_1478
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.event-of
d_event'45'of_1380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_event'45'of_1380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_event'45'of_1380
du_event'45'of_1380 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_event'45'of_1380
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_354
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events
d_flat'45'events_1382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events_1382 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_flat'45'events_1382 v1
du_flat'45'events_1382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events_1382 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_360 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events-fetch
d_flat'45'events'45'fetch_1384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'fetch_1384 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_flat'45'events'45'fetch_1384 v1
du_flat'45'events'45'fetch_1384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events'45'fetch_1384 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'fetch_364
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch._.flat-events-step
d_flat'45'events'45'step_1388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'events'45'step_1388 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_flat'45'events'45'step_1388 v1
du_flat'45'events'45'step_1388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_flat'45'events'45'step_1388 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events'45'step_362
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.call≢thunk
d_call'8802'thunk_1394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'8802'thunk_1394 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.ret≢thunk
d_ret'8802'thunk_1402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ret'8802'thunk_1402 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-agree
d_events'45'agree_1456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'agree_1456 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16 v17 v18 v19 v20
  = du_events'45'agree_1456
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_events'45'agree_1456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'agree_1456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17 v18
  = case coe v11 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             erased
      _ -> let v19 = subInt (coe v11) (coe (1 :: Integer)) in
           coe
             (coe
                du_go'45'h_1894 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v19)
                (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
                (coe v18)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-running
d_events'45'running_1474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running_1474 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
                         v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21
  = du_events'45'running_1474
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_events'45'running_1474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running_1474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18
  = coe
      du_go_1928 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214 (coe v14)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v15)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.events-running-fetch
d_events'45'running'45'fetch_1494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'fetch_1494 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
                                  v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_events'45'running'45'fetch_1494
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_events'45'running'45'fetch_1494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'fetch_1494 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = case coe v17 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2288
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1474
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2290
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1484
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2292
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'output'45'to'45'input2_1504
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2294
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'input2'45'to'45'output_1494
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296
        -> coe
             du_load'45'indirect'45'step_1688 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298
        -> coe
             du_load'45'indirect'45'suc'45'step_1706 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300 v20
        -> coe
             du_load'45'from'45'slot'45'step_1726 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v20) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2302 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1742
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3126
                   (coe v0) (coe v15) (coe v20)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304
        -> coe
             du_store'45'indirect'45'step_1784 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306
        -> coe
             du_store'45'indirect'45'suc'45'step_1802 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2308 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1604
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                   (coe v19)))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310 v20
        -> coe
             du_restore'45'input'45'step_1746 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v20) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2312 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2314 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2316 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1568
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2318 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2320
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
        -> coe
             du_call'45'step_1574 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v18)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2324 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1580
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2326 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1756
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3126
                   (coe v0) (coe v15) (coe v20)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328 v20
        -> coe
             du_worklist'45'pop'45'step_1766 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
             (coe v20) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2330 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1592
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336 v20 v21 v22
        -> coe
             du_sigop'45'step_1826 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v20)
             (coe v21) (coe v22) (coe v18) (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340 v20 v21 v22
        -> case coe v21 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v21) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_1974
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v22 v18 erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lit'45'fits_1930
                          v9 v10 v14 v15 v16 v22
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                             (coe v19))
                          v18 erased))
                    (coe v19)
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2340
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v21) (coe v22))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_1986
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v22 v18 erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_float'45'fits_1942
                          v9 v10 v14 v15 v16 v22
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                             (coe v19))
                          v18 erased))
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342 v20
        -> coe
             du_go_2618 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
             (coe v13) (coe v14) (coe v15) (coe v16) (coe v20) (coe v18)
             (coe v19)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_208 (coe v1)
                (coe v14) (coe v20))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1614
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v18 erased erased)
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2346 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1626
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_tag'45'fits_1918
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19))
                   v18 erased))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2348 v20 v21
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2350 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_extend'45'view_4020
                (coe v2) (coe v10)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
                (coe v20)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1838
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19))
                   v18 erased))
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2046
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v18 erased erased
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_612
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_612
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input2_58))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_612
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
                (coe
                   MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'regs_612
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
                      (coe v19))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'closure_1074
                   (coe v19))
                (\ v21 v22 ->
                   coe
                     MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'heap_616
                     (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
                        (coe v19))
                     v21)
                (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_wf'45'stack_622
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'wf_1072
                      (coe v19)))
                erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_heap'45'room_1838
                   v9 v10 v14 v15 v16 v20
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19))
                   v18 erased)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_lo'45'fits_1952
                   v9 v10 v14 v15 v16
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19))
                   v18))
             (coe v19)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2352 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_450
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1514
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_452
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1524
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454
               -> coe
                    du_scratch'45'dec'45'step_1652 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_456
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1544
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_458
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1534
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460
               -> coe
                    du_count'45'inc'45'step_1670 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
                    (coe v18) (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v21
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v17)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1556
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v21 v18 erased erased)
                    (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v21
               -> coe
                    du_cjmp'45'step_1594 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v21
               -> coe
                    du_branch'45'step_1614 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v21
               -> coe
                    du_tag'45'branch'45'step_1634 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
                    (coe v21) (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v21 v22
               -> coe
                    du_thunk'45'step_1536 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v22) (coe v18) (coe v19)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 v21
               -> coe
                    du_ret'45'step_1556 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v21)
                    (coe v18) (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2358 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.ccc-step-bs
d_ccc'45'step'45'bs_1514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ccc'45'step'45'bs_1514 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
                         v12 v13 v14 v15 v16 v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_ccc'45'step'45'bs_1514
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v21
du_ccc'45'step'45'bs_1514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ccc'45'step'45'bs_1514 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
               (coe v6))
            (coe v16))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_3046 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.thunk-step
d_thunk'45'step_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'step_1536 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                     v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_thunk'45'step_1536
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22
du_thunk'45'step_1536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'step_1536 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17 v18 v19 v20
  = coe
      du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1538
         (coe v10)
         (coe
            du_lo''_3094 (coe v2) (coe v4) (coe v7) (coe v10) (coe v16)
            (coe v18))
         (coe
            du_front'45'lo''_3100 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10)
            (coe v14) (coe v15) (coe v16) (coe v17) (coe v18) (coe v19)
            (coe v20)))
      (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 (coe v17)
            (coe v18)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1940
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
            (coe v9))
         v10 v14 v15 v16 v17 v18
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_link_3084 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
               (coe v17) (coe v18) (coe v20)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_pend_3086 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
               (coe v17) (coe v18) (coe v20)))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_pend_3086 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
                  (coe v17) (coe v18) (coe v20))))
         v19 erased erased
         (coe
            du_lo''_3094 (coe v2) (coe v4) (coe v7) (coe v10) (coe v16)
            (coe v18))
         (coe
            du_lo'''8804'lo_3096 (coe v2) (coe v4) (coe v7) (coe v10) (coe v16)
            (coe v18))
         (coe
            du_front'45'lo''_3100 (coe v2) (coe v4) (coe v7) (coe v9) (coe v10)
            (coe v14) (coe v15) (coe v16) (coe v17) (coe v18) (coe v19)
            (coe v20))
         (coe
            du_lo'''8804'rsp_3098 (coe v2) (coe v4) (coe v7) (coe v10)
            (coe v16) (coe v18))
         (coe
            du_fits_3090 (coe v2) (coe v9) (coe v10) (coe v14) (coe v15)
            (coe v16) (coe v17) (coe v18) (coe v19) (coe v20))
         erased
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1874
            v9 v10 v14 v15 v16
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v4))
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
               (coe v20))
            v19)
         erased erased)
      (coe v20)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.ret-step
d_ret'45'step_1556 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ret'45'step_1556 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_ret'45'step_1556
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_ret'45'step_1556 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ret'45'step_1556 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19
  = coe
      du_go_3172 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
      (coe v19)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_ret'45'site'45'owes_1296
         v0 v1 v2 erased v14 v15 v17
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
            (coe v19))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.call-step
d_call'45'step_1574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'step_1574 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_call'45'step_1574
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_call'45'step_1574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'step_1574 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 v15 v16 v17 v18
  = coe
      du_go_3252 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
      (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_call'45'site'45'shape_1284
         v0 v1 v2 erased v14 v15
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
            (coe v18))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.cjmp-step
d_cjmp'45'step_1594 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cjmp'45'step_1594 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_cjmp'45'step_1594
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_cjmp'45'step_1594 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cjmp'45'step_1594 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                     v14 v15 v16 v17 v18 v19
  = coe
      du_go'45'fl_3336 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v1)
         (coe v14) (coe v17))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.branch-step
d_branch'45'step_1614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_branch'45'step_1614 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                      v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_branch'45'step_1614
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_branch'45'step_1614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_branch'45'step_1614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15 v16 v17 v18 v19
  = coe
      du_go'45'sv_3476 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.tag-branch-step
d_tag'45'branch'45'step_1634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag'45'branch'45'step_1634 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                             v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_tag'45'branch'45'step_1634
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_tag'45'branch'45'step_1634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_tag'45'branch'45'step_1634 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                              v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      du_go'45'loc_3654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_3524 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
            (coe v19)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_3524 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
               (coe v19))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.scratch-dec-step
d_scratch'45'dec'45'step_1652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_scratch'45'dec'45'step_1652 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                              v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_scratch'45'dec'45'step_1652
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_scratch'45'dec'45'step_1652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_scratch'45'dec'45'step_1652 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12 v13 v14 v15 v16 v17 v18
  = coe
      du_go'45'sv_3736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.count-inc-step
d_count'45'inc'45'step_1670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_count'45'inc'45'step_1670 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_count'45'inc'45'step_1670
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_count'45'inc'45'step_1670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_count'45'inc'45'step_1670 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14 v15 v16 v17 v18
  = coe
      du_go'45'sv_3786 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Count_64))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-indirect-step
d_load'45'indirect'45'step_1688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'step_1688 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_load'45'indirect'45'step_1688
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_load'45'indirect'45'step_1688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'step_1688 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13 v14 v15 v16 v17 v18
  = coe
      du_go'45'loc_3948 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_3832 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
            (coe v18)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_3832 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
               (coe v18))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-indirect-suc-step
d_load'45'indirect'45'suc'45'step_1706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'indirect'45'suc'45'step_1706 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8
                                       v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_load'45'indirect'45'suc'45'step_1706
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_load'45'indirect'45'suc'45'step_1706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'indirect'45'suc'45'step_1706 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
  = coe
      du_go'45'loc_4106 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_wits_3990 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
            (coe v18)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_wits_3990 (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
               (coe v18))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.load-from-slot-step
d_load'45'from'45'slot'45'step_1726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_load'45'from'45'slot'45'step_1726 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
                                    v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_load'45'from'45'slot'45'step_1726
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_load'45'from'45'slot'45'step_1726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_load'45'from'45'slot'45'step_1726 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      du_go'45'mem_4154 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
         v17)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.restore-input-step
d_restore'45'input'45'step_1746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_restore'45'input'45'step_1746 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_restore'45'input'45'step_1746
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_restore'45'input'45'step_1746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_restore'45'input'45'step_1746 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      du_go'45'mem_4206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
         v17)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.worklist-pop-step
d_worklist'45'pop'45'step_1766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_worklist'45'pop'45'step_1766 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                               v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23
  = du_worklist'45'pop'45'step_1766
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_worklist'45'pop'45'step_1766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_worklist'45'pop'45'step_1766 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      du_go'45'mem_4258 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
         (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
         v17)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.store-indirect-step
d_store'45'indirect'45'step_1784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'step_1784 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9
                                 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_store'45'indirect'45'step_1784
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_store'45'indirect'45'step_1784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'step_1784 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12 v13 v14 v15 v16 v17 v18
  = coe
      du_go'45'ptr_4308 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.store-indirect-suc-step
d_store'45'indirect'45'suc'45'step_1802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_store'45'indirect'45'suc'45'step_1802 v0 v1 v2 v3 ~v4 ~v5 v6 v7
                                        v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22
  = du_store'45'indirect'45'suc'45'step_1802
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
du_store'45'indirect'45'suc'45'step_1802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_store'45'indirect'45'suc'45'step_1802 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
  = coe
      du_go'45'ptr_4382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.sigop-step
d_sigop'45'step_1826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'step_1826 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                     v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_sigop'45'step_1826
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23
du_sigop'45'step_1826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'step_1826 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                      v14 v15 v16 v17 v18 v19 v20 v21
  = coe
      du_go'45'eff_4462 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
      (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
      (coe v18) (coe v19) (coe v20) (coe v21)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v19))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch.sigop-external
d_sigop'45'external_1850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'external_1850 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
                         v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_sigop'45'external_1850
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23
du_sigop'45'external_1850 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'external_1850 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                          v13 v14 v15 v16 v17 v18 v19 v20 v21
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_rec_4514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
               (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
               (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
               (coe v19) (coe v20) (coe v21))))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-h
d_go'45'h_1894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'h_1894 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17 v18 v19 v20 v21 ~v22
  = du_go'45'h_1894
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21
du_go'45'h_1894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'h_1894 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19
  = if coe v19
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
             erased
      else coe
             du_events'45'running_1474 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
             (coe v17) (coe v18)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_1928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1928 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 ~v21 v22 ~v23
  = du_go_1928
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v22
du_go_1928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1928 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
        -> coe
             du_events'45'running'45'fetch_1494 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
             (coe v10) (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe v16) (coe v20) (coe v17) (coe v18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_events'45'running'45'end_1246
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_2618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2618 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go_2618
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go_2618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2618 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2342
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2000
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v17
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
                      (coe v6))
                   (coe v14) (coe v21))
                v18 erased erased erased)
             (coe v19)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.has-body
d_has'45'body_2632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_has'45'body_2632 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 ~v23 ~v24
  = du_has'45'body_2632 v0 v1 v2 v17 v19 v21
du_has'45'body_2632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_has'45'body_2632 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_emitted'45'code'45'addr'45'has'45'body_1320
      v0 v1 v2 erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_302
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
            (coe v5)))
      (MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v3)) v4 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.no-body
d_no'45'body_2642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'body_2642 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._._.nj
d_nj_2654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nj_2654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28 ~v29
  = du_nj_2654
du_nj_2654 :: AgdaAny
du_nj_2654 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_3046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_3046 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_rec_3046
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v19 v20 v21
du_rec_3046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_3046 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18
  = coe
      du_events'45'agree_1456 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe v11) (coe v12) (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1080 v1
         v16 v14 v15)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v17))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v17)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1096
         (coe v1) (coe v16) (coe v14) (coe v15) (coe v18))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.result
d_result_3048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_result_3048 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.link
d_link_3084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_link_3084 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16 v17 ~v18 v19 v20 ~v21 v22 ~v23 ~v24
  = du_link_3084 v0 v1 v2 v16 v17 v19 v20 v22
du_link_3084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_link_3084 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_thunk'45'entry'45'link_2348
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.pend
d_pend_3086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pend_3086 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16 v17 ~v18 v19 v20 ~v21 v22 ~v23 ~v24
  = du_pend_3086 v0 v1 v2 v16 v17 v19 v20 v22
du_pend_3086 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pend_3086 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_thunk'45'entry'45'ret_2374
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.room
d_room_3088 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_3088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_room_3088 v11 v12 v16 v17 v18 v19 v20 v21 v22
du_room_3088 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_3088 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_stack'45'room_1852
      v0 v1 v2 v3 v4 v5 v6
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v8))
      v7 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.fits
d_fits_3090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_3090 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_fits_3090 v2 v11 v12 v16 v17 v18 v19 v20 v21 v22
du_fits_3090 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_3090 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_50
            (coe v0) (coe v7)))
      (coe
         du_room_3088 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-rsp
d_front'45'rsp_3092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_3092 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_front'45'rsp_3092 v11 v12 v16 v17 v18 v19 v20 v21 v22
du_front'45'rsp_3092 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_3092 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_394
         (coe v1))
      (coe
         du_room_3088 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'
d_lo''_3094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_3094 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24
  = du_lo''_3094 v2 v6 v9 v12 v18 v20
du_lo''_3094 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny -> Integer -> Integer
du_lo''_3094 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_50
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'≤lo
d_lo'''8804'lo_3096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_3096 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24
  = du_lo'''8804'lo_3096 v2 v6 v9 v12 v18 v20
du_lo'''8804'lo_3096 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_3096 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_50
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.lo'≤rsp
d_lo'''8804'rsp_3098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_3098 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24
  = du_lo'''8804'rsp_3098 v2 v6 v9 v12 v18 v20
du_lo'''8804'rsp_3098 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_3098 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_50
            (coe v0) (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.front-lo'
d_front'45'lo''_3100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_3100 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22 ~v23 ~v24
  = du_front'45'lo''_3100
      v2 v6 v9 v11 v12 v16 v17 v18 v19 v20 v21 v22
du_front'45'lo''_3100 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_3100 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_394
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v7
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_50
            (coe v0) (coe v9)))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_414
         (coe v4))
      (coe
         du_front'45'rsp_3092 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.saved-cons
d_saved'45'cons_3144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1412 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_saved'45'cons_3144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                     v24 ~v25 v26 ~v27 ~v28 ~v29
  = du_saved'45'cons_3144 v24 v26
du_saved'45'cons_3144 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.T_RetMatch_1412 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_saved'45'cons_3144 v0 v1
  = coe
      seq (coe v1)
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_3172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_3172 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24
  = du_go_3172
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go_3172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_3172 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
        -> case coe v22 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
               -> coe
                    du_go'45'sv_3192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
                    (coe v18) (coe v19) (coe v21) (coe v23)
                    (coe
                       du_saved'45'cons_3144
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
                          (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.d_seg'45'stack_1478
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_run'45'seg'45'wf_1800
                             (coe v0) (coe v1) (coe v2) (coe v14) (coe v15)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                                (coe v19)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.go-sv
d_go'45'sv_3192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_3192 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 v27
  = du_go'45'sv_3192
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24 v25 v27
du_go'45'sv_3192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_3192 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21 v22
  = case coe v22 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
        -> case coe v24 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
               -> case coe v26 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                      -> coe
                           du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                           (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 (coe v17)))
                           (coe
                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_1962
                              (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                                 (coe v9))
                              v10 v14 v15 v16 v17 v20 v21 v23 v25 v27 v18 erased erased erased
                              erased erased
                              (coe
                                 MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_ret'45'no'45'wrap_1896
                                 v9 v10 v14 v15 v16 v17
                                 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                                    (coe v19))
                                 v18 erased)
                              erased)
                           (coe v19)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._._.hpost
d_hpost_3206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3206 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go
d_go_3252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_3252 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
          v16 v17 v18 v19 v20 ~v21 ~v22 v23
  = du_go_3252
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23
du_go_3252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_3252 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
        -> case coe v21 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
               -> case coe v23 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                      -> case coe v25 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                             -> coe
                                  seq (coe v27)
                                  (coe
                                     du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1538
                                        (coe v10)
                                        (coe
                                           du_lo''_3276 (coe v2) (coe v4) (coe v7) (coe v10)
                                           (coe v16))
                                        (coe
                                           du_front'45'lo''_3282 (coe v2) (coe v4) (coe v7) (coe v9)
                                           (coe v10) (coe v14) (coe v15) (coe v16) (coe v17)
                                           (coe v18)))
                                     (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322)
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2022
                                        (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                                           (coe v9))
                                        v10 v14 v15 v16 v20 v22 v24 v17 erased erased erased erased
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1060
                                           (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                                              (coe v17))
                                           (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92
                                              (coe v20))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80
                                              (coe v22))
                                           erased)
                                        erased
                                        (coe
                                           du_lo''_3276 (coe v2) (coe v4) (coe v7) (coe v10)
                                           (coe v16))
                                        (coe
                                           du_lo'''8804'lo_3278 (coe v2) (coe v4) (coe v7) (coe v10)
                                           (coe v16))
                                        (coe
                                           du_front'45'lo''_3282 (coe v2) (coe v4) (coe v7) (coe v9)
                                           (coe v10) (coe v14) (coe v15) (coe v16) (coe v17)
                                           (coe v18))
                                        (coe
                                           du_lo'''8804'rsp_3280 (coe v2) (coe v4) (coe v7)
                                           (coe v10) (coe v16))
                                        (coe
                                           du_fits_3272 (coe v2) (coe v9) (coe v10) (coe v14)
                                           (coe v15) (coe v16) (coe v17) (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1874
                                           v9 v10 v14 v15 v16
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
                                              (coe v4))
                                           (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                                              (coe v18))
                                           v17)
                                        erased)
                                     (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.room
d_room_3270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_room_3270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28
  = du_room_3270 v11 v12 v16 v17 v18 v19 v20
du_room_3270 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_room_3270 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_call'45'room_1862
      v0 v1 v2 v3 v4
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v6))
      v5 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.fits
d_fits_3272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fits_3272 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28
  = du_fits_3272 v2 v11 v12 v16 v17 v18 v19 v20
du_fits_3272 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fits_3272 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 (coe v0))
      (coe
         du_room_3270 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-rsp
d_front'45'rsp_3274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'rsp_3274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28
  = du_front'45'rsp_3274 v11 v12 v16 v17 v18 v19 v20
du_front'45'rsp_3274 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'rsp_3274 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_394
         (coe v1))
      (coe
         du_room_3270 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'
d_lo''_3276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_lo''_3276 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26
            ~v27 ~v28
  = du_lo''_3276 v2 v6 v9 v12 v18
du_lo''_3276 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny -> Integer
du_lo''_3276 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'≤lo
d_lo'''8804'lo_3278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'lo_3278 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                    v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                    ~v26 ~v27 ~v28
  = du_lo'''8804'lo_3278 v2 v6 v9 v12 v18
du_lo'''8804'lo_3278 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'lo_3278 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.lo'≤rsp
d_lo'''8804'rsp_3280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'''8804'rsp_3280 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 ~v11
                     v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28
  = du_lo'''8804'rsp_3280 v2 v6 v9 v12 v18
du_lo'''8804'rsp_3280 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'''8804'rsp_3280 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v4
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.front-lo'
d_front'45'lo''_3282 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo''_3282 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10 v11
                     v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
                     ~v26 ~v27 ~v28
  = du_front'45'lo''_3282 v2 v6 v9 v11 v12 v16 v17 v18 v19 v20
du_front'45'lo''_3282 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'45'lo''_3282 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'8851''45'operator_4580)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_394
         (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_412
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
            v2 v7
            (coe
               MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
               (coe v1)))
         v0)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_414
         (coe v4))
      (coe
         du_front'45'rsp_3274 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
         (coe v8) (coe v9))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.step-eq
d_step'45'eq_3284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45'eq_3284 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3292 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_3336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_3336 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'fl_3336
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go'45'fl_3336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_3336 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 (coe v17)))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1826
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v17 v21 v18 erased erased erased)
             (coe v19)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'jmp_1572
             (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1826
                (coe v9))
             v10 v12 v13 v14 v15 v16 v17 v18 erased erased erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3346 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3358 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_3398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_3398 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25 v26 ~v27
  = du_go'45'fl_3398
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24 v26
du_go'45'fl_3398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_3398 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21
  = case coe v20 of
      0 -> case coe v21 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278
                          (coe v17)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1842
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v17 (0 :: Integer) v22 v18 erased erased erased
                       erased)
                    (coe v19)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'scratch'45'zero_1588
                    (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1826
                       (coe v9))
                    v10 v12 v13 v14 v15 v16 v17 v18 erased erased erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v22 = subInt (coe v20) (coe (1 :: Integer)) in
           coe
             (case coe v21 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                  -> coe
                       du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                       (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278
                             (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1842
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                             (coe v9))
                          v10 v14 v15 v16 v17 v20 v23 v18 erased erased erased erased)
                       (coe v19)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                       (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278
                             (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1856
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                             (coe v9))
                          v10 v14 v15 v16 v17 v22 v18 erased erased erased)
                       (coe v19)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3410 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3410 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3432 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3448 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3462 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_3476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_3476 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'sv_3476
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go'45'sv_3476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_3476 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v21
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v21
        -> coe
             du_go'45'fl_3398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v18) (coe v19) (coe v21)
             (coe
                MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v1)
                (coe v14) (coe v17))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v21 v22 v23
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v21
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_3524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_3524 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_wits_3524 v0 v1 v2 v16 v17 v21
du_wits_3524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_3524 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_branch'45'tag'45'scrutinee'45'wf_4072
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-fl
d_go'45'fl_3534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'fl_3534 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 ~v27 ~v28 v29
                ~v30
  = du_go'45'fl_3534
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24 v25 v29
du_go'45'fl_3534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'fl_3534 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19 v20 v21 v22
  = case coe v21 of
      0 -> case coe v22 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280
                          (coe v17)))
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1874
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v17 v20 (0 :: Integer) v23 v18 erased erased erased
                       erased erased erased)
                    (coe v19)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'c'45'branch'45'tag'45'zero_1606
                    (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1826
                       (coe v9))
                    v10 v12 v13 v14 v15 v16 v17 v20 v18 erased erased erased erased
                    erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v23 = subInt (coe v21) (coe (1 :: Integer)) in
           coe
             (case coe v22 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v24
                  -> coe
                       du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                       (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280
                             (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1874
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                             (coe v9))
                          v10 v14 v15 v16 v17 v20 v21 v24 v18 erased erased erased erased
                          erased erased)
                       (coe v19)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                       (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280
                             (coe v17)))
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1890
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                             (coe v9))
                          v10 v14 v15 v16 v17 v20 v23 v18 erased erased erased erased erased)
                       (coe v19)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3552 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3584 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3584 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3610 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3634 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_3654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_3654 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 v25 ~v26 ~v27
  = du_go'45'loc_3654
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24 v25
du_go'45'loc_3654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_3654 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20 v21
  = coe
      seq (coe v20)
      (coe
         du_go'45'fl_3534 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
         (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
         (coe v18) (coe v19) (coe v20) (coe v21)
         (coe
            MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'label_162 (coe v1)
            (coe v14) (coe v17)))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.dc
d_dc_3668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_dc_3668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27
  = du_dc_3668 v20
du_dc_3668 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_dc_3668 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.addr-val
d_addr'45'val_3670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'val_3670 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rd-heap
d_rd'45'heap_3672 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'heap_3672 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.dc
d_dc_3688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
d_dc_3688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 ~v28
  = du_dc_3688 v20
du_dc_3688 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_982
du_dc_3688 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.spc
d_spc_3690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_spc_3690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           ~v26 ~v27 ~v28
  = du_spc_3690
du_spc_3690 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_spc_3690
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3082
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.st-cf
d_st'45'cf_3692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_st'45'cf_3692 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rdi-val
d_rdi'45'val_3696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rdi'45'val_3696 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rd-stack
d_rd'45'stack_3704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rd'45'stack_3704 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_3736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_3736 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24
  = du_go'45'sv_3736
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23
du_go'45'sv_3736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_3736 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_454))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1902
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v17 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_scratch'45'dec'45'guarded_1884
                   v9 v10 v14 v15 v16
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v18))
                   v17 erased)
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_reg'45'range_1874
                   v9 v10 v14 v15 v16
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_50
                      (coe v4))
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v18))
                   v17))
             (coe v18)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v20 v21 v22
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-sv
d_go'45'sv_3786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'sv_3786 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24
  = du_go'45'sv_3786
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23
du_go'45'sv_3786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'sv_3786 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15 v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v20
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2354
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_460))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1914
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v20 v17 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_count'45'no'45'wrap_1906
                   v9 v10 v14 v15 v16
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v18))
                   v17 erased))
             (coe v18)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v20 v21 v22
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_3832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_3832 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_wits_3832 v0 v1 v2 v16 v17 v20
du_wits_3832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_3832 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'target'45'wf_4164
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3840 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24 v25 v26 ~v27
  = du_go'45'mem_3840
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23 v25 v26
du_go'45'mem_3840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3840 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20 v21
  = case coe v21 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1640
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v19 v22 v17 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1060
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                      (coe v17))
                   v19 v22 erased)
                erased)
             (coe v18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect_1540
             (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1826
                (coe v9))
             v10 v12 v13 v14 v15 v16 v19 v17 erased erased erased
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1064
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                   (coe v17))
                v19 v20)
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3856 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3878 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-stack
d_go'45'stack_3896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_3896 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 v24 ~v25 v26 v27 ~v28
  = du_go'45'stack_3896
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23 v24 v26 v27
du_go'45'stack_3896 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_3896 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19 v20 v21 v22
  = case coe v21 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
        -> case coe v22 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2296)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1656
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v19 v20 v25 v17 erased erased erased erased v24
                       erased)
                    (coe v18)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_3916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_3916 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_3948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_3948 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24 v25
  = du_go'45'loc_3948
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23 v25
du_go'45'loc_3948 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_3948 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20
  = case coe v19 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v21 v22
        -> coe
             du_go'45'stack_3896 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v18) (coe v21) (coe v22)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3082)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
                v22)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v21
        -> coe
             du_go'45'mem_3840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v18) (coe v21) (coe v20 v21 erased)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15)) v21)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.wits
d_wits_3990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wits_3990 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16 v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_wits_3990 v0 v1 v2 v16 v17 v20
du_wits_3990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wits_3990 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_load'45'indirect'45'suc'45'target'45'wf_4202
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_3998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_3998 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24 v25 v26 ~v27
  = du_go'45'mem_3998
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23 v25 v26
du_go'45'mem_3998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_3998 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20 v21
  = case coe v21 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1670
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v19 v22 v17 erased erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1060
                   (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                      (coe v17))
                   (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v19)) v22
                   erased)
                erased)
             (coe v18)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_st'45'load'45'indirect'45'suc_1556
             (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_sts_1826
                (coe v9))
             v10 v12 v13 v14 v15 v16 v19 v17 erased erased erased
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1064
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                   (coe v17))
                (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v19)) v20)
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4014 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4014 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4036 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4036 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-stack
d_go'45'stack_4054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'stack_4054 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 v24 ~v25 v26 v27 ~v28
  = du_go'45'stack_4054
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23 v24 v26 v27
du_go'45'stack_4054 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'stack_4054 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16 v17 v18 v19 v20 v21 v22
  = case coe v21 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
        -> case coe v22 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v25
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2298)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1686
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v19 v20 v25 v17 erased erased erased erased v24
                       erased)
                    (coe v18)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4074 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4074 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-loc
d_go'45'loc_4106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'loc_4106 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24 v25
  = du_go'45'loc_4106
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23 v25
du_go'45'loc_4106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'loc_4106 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20
  = case coe v19 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v21 v22
        -> coe
             du_go'45'stack_4054 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v18) (coe v21) (coe v22)
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3104)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))
                (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                   (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v15)))
                (addInt (coe (1 :: Integer)) (coe v22)))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v21
        -> coe
             du_go'45'mem_3998 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v17)
             (coe v18) (coe v21) (coe v20 v21 erased)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                (MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v15))
                (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v21)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_4154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_4154 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'mem_4154
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go'45'mem_4154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_4154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2300
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1700
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v17 v21 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3126
                   (coe v0) (coe v15) (coe v17)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4164 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_4206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_4206 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'mem_4206
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go'45'mem_4206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_4206 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2310
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1714
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v17 v21 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3126
                   (coe v0) (coe v15) (coe v17)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4216 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-mem
d_go'45'mem_4258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'mem_4258 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 v21 ~v22 ~v23 v24 ~v25
  = du_go'45'mem_4258
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v24
du_go'45'mem_4258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'mem_4258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20
  = case coe v20 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
        -> coe
             du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2328
                (coe v17))
             (coe
                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1728
                (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                   (coe v9))
                v10 v14 v15 v16 v17 v21 v18 erased erased
                (coe
                   MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_slot'45'read'45'in'45'frame_3126
                   (coe v0) (coe v15) (coe v17)
                   (coe
                      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                      (coe v19)))
                erased)
             (coe v19)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4268 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-ptr
d_go'45'ptr_4308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_4308 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24
  = du_go'45'ptr_4308
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23
du_go'45'ptr_4308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_4308 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v21 v22
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1784
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v21 v22 v17 erased erased erased erased
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current_3082))
                       erased)
                    (coe v18)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v21
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2304)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1768
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v21 v17 erased erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1064
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                             (coe v17))
                          v21
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'inbounds_4122
                             (coe v0) (coe v1) (coe v14) (coe v15) (coe v21)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                                (coe v18))))
                       erased)
                    (coe v18)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v20 v21 v22
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4318 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4334 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-ptr
d_go'45'ptr_4382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'ptr_4382 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 ~v21 ~v22 v23 ~v24
  = du_go'45'ptr_4382
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v23
du_go'45'ptr_4382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'ptr_4382 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19
  = case coe v19 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v20
        -> case coe v20 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v21 v22
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1812
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v21 v22 v17 erased erased erased erased
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_stack'45'ptr'45'current'45'suc_3104))
                       erased)
                    (coe v18)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v21
               -> coe
                    du_ccc'45'step'45'bs_1514 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                    (coe v11) (coe v12) (coe v13) (coe v14) (coe v15)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2306)
                    (coe
                       MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1796
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_bss_1824
                          (coe v9))
                       v10 v14 v15 v16 v21 v17 erased erased erased
                       (coe
                          MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1064
                          (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_690
                             (coe v17))
                          (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v21))
                          (coe
                             MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunWF.du_store'45'indirect'45'suc'45'inbounds_4142
                             (coe v0) (coe v1) (coe v14) (coe v15)
                             (coe
                                MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
                                (coe v18))))
                       erased)
                    (coe v18)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v20 v21 v22
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v20
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4392 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.hpost
d_hpost_4408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hpost_4408 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.go-eff
d_go'45'eff_4462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'eff_4462 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25 v26 ~v27
  = du_go'45'eff_4462
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23 v26
du_go'45'eff_4462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'eff_4462 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                  v15 v16 v17 v18 v19 v20 v21 v22
  = case coe v22 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_rec_4474 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                      (coe v13) (coe v14) (coe v15) (coe v16) (coe v17) (coe v18)
                      (coe v19) (coe v20) (coe v21))))
             erased
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe
             du_sigop'45'external_1850 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
             (coe v17) (coe v18) (coe v19) (coe v20) (coe v21)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe
             du_sigop'45'external_1850 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
             (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
             (coe v17) (coe v18) (coe v19) (coe v20) (coe v21)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.contract
d_contract_4470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_4470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 ~v13 ~v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25 ~v26
  = du_contract_4470 v11 v12 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_contract_4470 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_4470 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_arith'45'sigop'45'contract_1972
      v0 v1 v2 v3 v4 v5 v6 v7 v8
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v10))
      erased erased v9 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.pl
d_pl_4472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_pl_4472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13
          ~v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25 ~v26
  = du_pl_4472 v11 v12 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_pl_4472 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  AgdaAny
du_pl_4472 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_contract_4470 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.rec
d_rec_4474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_4474 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25 ~v26
  = du_rec_4474
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23
du_rec_4474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_4474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19 v20 v21
  = coe
      du_events'45'agree_1456 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe v11) (coe v12) (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_526
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336
            (coe v17) (coe v18) (coe v19))
         (coe v15))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         v8
         (coe
            du_pl_4472 (coe v9) (coe v10) (coe v13) (coe v14) (coe v15)
            (coe v16) (coe v17) (coe v18) (coe v19) (coe v20) (coe v21))
         v16)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_4470 (coe v9) (coe v10) (coe v13) (coe v14) (coe v15)
               (coe v16) (coe v17) (coe v18) (coe v19) (coe v20) (coe v21))))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1096
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336
            (coe v17) (coe v18) (coe v19))
         (coe v14) (coe v15) (coe v21))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._._.goal
d_goal_4476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_4476 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.contract
d_contract_4512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_contract_4512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 ~v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_contract_4512 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
du_contract_4512 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_contract_4512 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_external'45'sigop'45'contract_1992
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.d_inv'45'run_1082
         (coe v11))
      erased erased v10 erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.rec
d_rec_4514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rec_4514 v0 v1 v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
           v16 v17 v18 v19 v20 v21 v22 v23 ~v24 ~v25
  = du_rec_4514
      v0 v1 v2 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
      v21 v22 v23
du_rec_4514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rec_4514 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
            v16 v17 v18 v19 v20 v21
  = coe
      du_events'45'agree_1456 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
      (coe v11) (coe v12) (coe v13) (coe v14)
      (coe
         MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'step'45'straight_526
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336
            (coe v17) (coe v18) (coe v19))
         (coe v15))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'past_440
         v8 v16)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_contract_4512 (coe v9) (coe v10) (coe v12) (coe v13) (coe v14)
               (coe v15) (coe v16) (coe v17) (coe v18) (coe v19) (coe v20)
               (coe v21))))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.du_flat'45'inv'45'step_1096
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2336
            (coe v17) (coe v18) (coe v19))
         (coe v14) (coe v15) (coe v21))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventDispatch.Dispatch._.goal
d_goal_4516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_Supply_1652 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_362 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_668 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.T_FlatInv_1050 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_goal_4516 = erased
