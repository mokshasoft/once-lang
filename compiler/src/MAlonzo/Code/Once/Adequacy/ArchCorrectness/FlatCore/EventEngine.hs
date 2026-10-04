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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EventEngine where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext
import qualified MAlonzo.Code.Once.Adequacy.FlatEvents
import qualified MAlonzo.Code.Once.Arith.Backend.RunTraceCore
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF
import qualified MAlonzo.Code.Once.CCC.Machine.FlatStoreWF
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.Instr
d_Instr_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Instr_34 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.compile-trace
d_compile'45'trace_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [AgdaAny]
d_compile'45'trace_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_compile'45'trace_38 v8
du_compile'45'trace_38 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [AgdaAny]
du_compile'45'trace_38 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'trace_108
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.mfetch
d_mfetch_60 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [AgdaAny] -> Integer -> Maybe AgdaAny
d_mfetch_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_mfetch_60 v8
du_mfetch_60 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [AgdaAny] -> Integer -> Maybe AgdaAny
du_mfetch_60 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.State
d_State_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_State_74 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.exec
d_exec_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> [AgdaAny] -> AgdaAny -> Maybe AgdaAny
d_exec_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_exec_76 v9
du_exec_76 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  Integer -> [AgdaAny] -> AgdaAny -> Maybe AgdaAny
du_exec_76 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_exec_300
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.memory
d_memory_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> Integer -> Maybe Integer
d_memory_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_memory_92 v9
du_memory_92 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> Integer -> Maybe Integer
du_memory_92 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_memory_290
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.mexecInstr
d_mexecInstr_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
d_mexecInstr_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_mexecInstr_94 v9
du_mexecInstr_94 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> Maybe AgdaAny
du_mexecInstr_94 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.rreg
d_rreg_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> AgdaAny -> Integer
d_rreg_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_rreg_96 v9
du_rreg_96 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> AgdaAny -> Integer
du_rreg_96 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.xhalted
d_xhalted_98 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> Bool
d_xhalted_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_xhalted_98 v9
du_xhalted_98 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> Bool
du_xhalted_98 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.xpc
d_xpc_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny -> Integer
d_xpc_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_xpc_100 v9
du_xpc_100 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  AgdaAny -> Integer
du_xpc_100 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.all-headView
d_all'45'headView_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_all'45'headView_126 v8
du_all'45'headView_126 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_126 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_all'45'headView_942
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_headView_182
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.blk-len
d_blk'45'len_128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer
d_blk'45'len_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_blk'45'len_128 v8
du_blk'45'len_128 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Integer
du_blk'45'len_128 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'len_124
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.blk-off
d_blk'45'off_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> Integer
d_blk'45'off_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_blk'45'off_130 v8
du_blk'45'off_130 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> Integer
du_blk'45'off_130 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_blk'45'off_128
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_compile'45'abstract_106
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.blk-off-suc
d_blk'45'off'45'suc_132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blk'45'off'45'suc_132 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.cons-step
d_cons'45'step_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cons'45'step_134 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.drop-+
d_drop'45''43'_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_136 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.drop-[]
d_drop'45''91''93'_138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_138 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.drop-compile
d_drop'45'compile_140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_140 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.drop-fetch
d_drop'45'fetch_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_142 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.drop-len-++
d_drop'45'len'45''43''43'_144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_144 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-at-offset
d_fetch'45'at'45'offset_146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_146 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-2nd
d_fetch'45'block'45'2nd_148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_148 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-3rd
d_fetch'45'block'45'3rd_150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_150 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-4th
d_fetch'45'block'45'4th_152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_152 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-5th
d_fetch'45'block'45'5th_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_154 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-6th
d_fetch'45'block'45'6th_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_156 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-head
d_fetch'45'block'45'head_158 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_158 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-block-nth
d_fetch'45'block'45'nth_160 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'nth_160 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-drop
d_fetch'45'drop_162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [AgdaAny] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_162 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-label-corr
d_find'45'label'45'corr_164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_164 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-label-go-skip
d_find'45'label'45'go'45'skip_166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [AgdaAny] ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_166 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-label-none-corr
d_find'45'label'45'none'45'corr_168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_168 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-label-none-go
d_find'45'label'45'none'45'go_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_170 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-label-pres
d_find'45'label'45'pres_172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_find'45'label'45'pres_172
du_find'45'label'45'pres_172 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_172 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'label'45'pres_788
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-thunk-corr
d_find'45'thunk'45'corr_174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_174 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.find-thunk-pres
d_find'45'thunk'45'pres_176 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_find'45'thunk'45'pres_176
du_find'45'thunk'45'pres_176 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_176 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition.du_find'45'thunk'45'pres_616
      v0 v1 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.hit-labelled
d_hit'45'labelled_178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hit'45'labelled_178 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.just-inj
d_just'45'inj_180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_180 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.skip-labelled
d_skip'45'labelled_182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'labelled_182 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.skip-plain
d_skip'45'plain_184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_skip'45'plain_184 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockStep
d_BlockStep_188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
d_BlockStep_188 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockStepAt
d_BlockStepAt_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
d_BlockStepAt_190 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps
d_BlockSteps_192 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.CompiledCorr
d_CompiledCorr_196 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                   a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.above-frontier-disj
d_above'45'frontier'45'disj_200 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_above'45'frontier'45'disj_200 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-alloc-heap
d_bs'45'alloc'45'heap_202 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
d_bs'45'alloc'45'heap_202 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2110
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-branch-nz
d_bs'45'c'45'branch'45'nz_204 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'nz_204 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-branch-scratch-zero
d_bs'45'c'45'branch'45'scratch'45'zero_206 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'scratch'45'zero_206 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1856
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-branch-tag-nz
d_bs'45'c'45'branch'45'tag'45'nz_208 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'nz_208 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1904
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-branch-tag-zero
d_bs'45'c'45'branch'45'tag'45'zero_210 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'zero_210 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1888
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-jmp
d_bs'45'c'45'jmp_212 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'jmp_212 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1840
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-label
d_bs'45'c'45'label_214 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'label_214 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-ret
d_bs'45'c'45'ret_216 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [Integer] ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'ret_216 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_2006
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-start
d_bs'45'c'45'start_218 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'start_218 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'start_1984
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-c-thunk
d_bs'45'c'45'thunk_220 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'c'45'thunk_220 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1966
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-call
d_bs'45'call_222 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'call_222 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2066
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-call-fn
d_bs'45'call'45'fn_224 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'call'45'fn_224 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call'45'fn_2086
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-count-inc
d_bs'45'count'45'inc_226 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'inc_226 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1928
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-count-zero
d_bs'45'count'45'zero_228 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'zero_228 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1548
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-lea-slot
d_bs'45'lea'45'slot_230 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'lea'45'slot_230 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1618
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-code-addr
d_bs'45'load'45'code'45'addr_232 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'code'45'addr_232 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2044
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-const
d_bs'45'load'45'const_234 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const_234 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_2018
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-const-float
d_bs'45'load'45'const'45'float_236 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const'45'float_236 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_2030
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-from-slot
d_bs'45'load'45'from'45'slot_238 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'from'45'slot_238 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1714
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-indirect
d_bs'45'load'45'indirect_240 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect_240 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-indirect-stack
d_bs'45'load'45'indirect'45'stack_242 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'stack_242 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1670
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-indirect-suc
d_bs'45'load'45'indirect'45'suc_244 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc_244 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1684
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-indirect-suc-stack
d_bs'45'load'45'indirect'45'suc'45'stack_246 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc'45'stack_246 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1700
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-load-tag-lit
d_bs'45'load'45'tag'45'lit_248 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'tag'45'lit_248 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1640
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-mov-to-input
d_bs'45'mov'45'to'45'input_250 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'input_250 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1518
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-mov-to-output
d_bs'45'mov'45'to'45'output_252 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'output_252 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1508
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-out-nz
d_bs'45'out'45'nz_254 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'out'45'nz_254 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'out'45'nz_1940
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-reclaim-to
d_bs'45'reclaim'45'to_256 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'reclaim'45'to_256 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1582
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-restore-input
d_bs'45'restore'45'input_258 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'restore'45'input_258 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1728
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-save-closure-reg
d_bs'45'save'45'closure'45'reg_260 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'save'45'closure'45'reg_260 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1628
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-scratch-dec
d_bs'45'scratch'45'dec_262 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'dec_262 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1916
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-scratch-load-count
d_bs'45'scratch'45'load'45'count_264 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'load'45'count_264 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1558
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-scratch-one
d_bs'45'scratch'45'one_266 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'one_266 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1528
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-scratch-zero
d_bs'45'scratch'45'zero_268 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'zero_268 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1538
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-store-at-slot
d_bs'45'store'45'at'45'slot_270 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'at'45'slot_270 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1756
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-store-indirect
d_bs'45'store'45'indirect_272 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect_272 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1782
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-store-indirect-stack
d_bs'45'store'45'indirect'45'stack_274 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'store'45'indirect'45'stack_274 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1798
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-store-indirect-suc
d_bs'45'store'45'indirect'45'suc_276 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'suc_276 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1810
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-store-indirect-suc-stack
d_bs'45'store'45'indirect'45'suc'45'stack_278 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'store'45'indirect'45'suc'45'stack_278 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1826
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-worklist-check
d_bs'45'worklist'45'check_280 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'check_280 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1606
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-worklist-init
d_bs'45'worklist'45'init_282 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'init_282 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1594
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-worklist-pop
d_bs'45'worklist'45'pop_284 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'pop_284 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.bs-worklist-push
d_bs'45'worklist'45'push_286 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'push_286 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1770
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.code-eq
d_code'45'eq_288 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_288 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.dataCorr
d_dataCorr_290 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dataCorr_290 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_694
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-just-drop
d_fetch'45'just'45'drop_292 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'just'45'drop_292 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch-nothing-drop
d_fetch'45'nothing'45'drop_294 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'nothing'45'drop_294 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.pc-off
d_pc'45'off_296 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_296 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.ret-eq
d_ret'45'eq_298 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  AgdaAny
d_ret'45'eq_298 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_698
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.slot-heap-disj
d_slot'45'heap'45'disj_300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'heap'45'disj_300 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.store-guard
d_store'45'guard_302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'guard_302 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-alloc-heap
d_bs'45'alloc'45'heap_306 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
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
d_bs'45'alloc'45'heap_306 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'alloc'45'heap_2110
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-branch-nz
d_bs'45'c'45'branch'45'nz_308 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'nz_308 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'nz_1870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-branch-scratch-zero
d_bs'45'c'45'branch'45'scratch'45'zero_310 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'scratch'45'zero_310 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'scratch'45'zero_1856
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-branch-tag-nz
d_bs'45'c'45'branch'45'tag'45'nz_312 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'nz_312 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'nz_1904
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-branch-tag-zero
d_bs'45'c'45'branch'45'tag'45'zero_314 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'branch'45'tag'45'zero_314 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'branch'45'tag'45'zero_1888
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-jmp
d_bs'45'c'45'jmp_316 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'jmp_316 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'jmp_1840
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-label
d_bs'45'c'45'label_318 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'label_318 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'label_1570
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-ret
d_bs'45'c'45'ret_320 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  Integer ->
  [Integer] ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'ret_320 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'ret_2006
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-start
d_bs'45'c'45'start_322 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'c'45'start_322 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'start_1984
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-c-thunk
d_bs'45'c'45'thunk_324 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'c'45'thunk_324 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'c'45'thunk_1966
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-call
d_bs'45'call_326 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'call_326 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call_2066
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-call-fn
d_bs'45'call'45'fn_328 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'call'45'fn_328 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'call'45'fn_2086
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-count-inc
d_bs'45'count'45'inc_330 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'inc_330 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'inc_1928
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-count-zero
d_bs'45'count'45'zero_332 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'count'45'zero_332 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'count'45'zero_1548
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-lea-slot
d_bs'45'lea'45'slot_334 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'lea'45'slot_334 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'lea'45'slot_1618
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-code-addr
d_bs'45'load'45'code'45'addr_336 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'code'45'addr_336 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'code'45'addr_2044
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-const
d_bs'45'load'45'const_338 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const_338 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const_2018
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-const-float
d_bs'45'load'45'const'45'float_340 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'const'45'float_340 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'const'45'float_2030
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-from-slot
d_bs'45'load'45'from'45'slot_342 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'from'45'slot_342 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'from'45'slot_1714
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-indirect
d_bs'45'load'45'indirect_344 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect_344 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect_1654
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-indirect-stack
d_bs'45'load'45'indirect'45'stack_346 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'stack_346 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'stack_1670
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-indirect-suc
d_bs'45'load'45'indirect'45'suc_348 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc_348 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc_1684
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-indirect-suc-stack
d_bs'45'load'45'indirect'45'suc'45'stack_350 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'indirect'45'suc'45'stack_350 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'indirect'45'suc'45'stack_1700
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-load-tag-lit
d_bs'45'load'45'tag'45'lit_352 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'load'45'tag'45'lit_352 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'load'45'tag'45'lit_1640
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-mov-to-input
d_bs'45'mov'45'to'45'input_354 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'input_354 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'input_1518
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-mov-to-output
d_bs'45'mov'45'to'45'output_356 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'mov'45'to'45'output_356 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'mov'45'to'45'output_1508
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-out-nz
d_bs'45'out'45'nz_358 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'out'45'nz_358 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'out'45'nz_1940
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-reclaim-to
d_bs'45'reclaim'45'to_360 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'reclaim'45'to_360 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'reclaim'45'to_1582
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-restore-input
d_bs'45'restore'45'input_362 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'restore'45'input_362 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'restore'45'input_1728
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-save-closure-reg
d_bs'45'save'45'closure'45'reg_364 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'save'45'closure'45'reg_364 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'save'45'closure'45'reg_1628
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-scratch-dec
d_bs'45'scratch'45'dec_366 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'dec_366 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'dec_1916
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-scratch-load-count
d_bs'45'scratch'45'load'45'count_368 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'load'45'count_368 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'load'45'count_1558
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-scratch-one
d_bs'45'scratch'45'one_370 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'one_370 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'one_1528
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-scratch-zero
d_bs'45'scratch'45'zero_372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'scratch'45'zero_372 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'scratch'45'zero_1538
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-store-at-slot
d_bs'45'store'45'at'45'slot_374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'at'45'slot_374 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'at'45'slot_1756
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-store-indirect
d_bs'45'store'45'indirect_376 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect_376 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect_1782
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-store-indirect-stack
d_bs'45'store'45'indirect'45'stack_378 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'store'45'indirect'45'stack_378 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'stack_1798
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-store-indirect-suc
d_bs'45'store'45'indirect'45'suc_380 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'store'45'indirect'45'suc_380 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc_1810
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-store-indirect-suc-stack
d_bs'45'store'45'indirect'45'suc'45'stack_382 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
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
d_bs'45'store'45'indirect'45'suc'45'stack_382 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'store'45'indirect'45'suc'45'stack_1826
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-worklist-check
d_bs'45'worklist'45'check_384 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'check_384 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'check_1606
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-worklist-init
d_bs'45'worklist'45'init_386 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'init_386 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'init_1594
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-worklist-pop
d_bs'45'worklist'45'pop_388 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'pop_388 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'pop_1742
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.BlockSteps.bs-worklist-push
d_bs'45'worklist'45'push_390 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bs'45'worklist'45'push_390 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_bs'45'worklist'45'push_1770
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.CompiledCorr.code-eq
d_code'45'eq_394 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'eq_394 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.CompiledCorr.dataCorr
d_dataCorr_396 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_dataCorr_396 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_dataCorr_694
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.CompiledCorr.pc-off
d_pc'45'off_398 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pc'45'off_398 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.CompiledCorr.ret-eq
d_ret'45'eq_400 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  AgdaAny
d_ret'45'eq_400 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.d_ret'45'eq_698
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.Emitted
d_Emitted_404 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_Emitted_404 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.EntryLike
d_EntryLike_406 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_EntryLike_406 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.LinkedImage
d_LinkedImage_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_LinkedImage_408 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.Reachable
d_Reachable_410 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.RunAt
d_RunAt_412 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.call-not-jmp
d_call'45'not'45'jmp_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'45'not'45'jmp_416 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.call-not-ret
d_call'45'not'45'ret_418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'45'not'45'ret_418 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.run-emit
d_run'45'emit_426 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_426 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.run-emitted
d_run'45'emitted_428 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'emitted_428 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
         (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
            (coe v0))
         erased)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.run-ir
d_run'45'ir_430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_430 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.run-linked
d_run'45'linked_432 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_432 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_444
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.run-reach
d_run'45'reach_434 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364
d_run'45'reach_434 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.run-tbl
d_run'45'tbl_436 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_436 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.RunAt.run-emit
d_run'45'emit_446 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'emit_446 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.RunAt.run-ir
d_run'45'ir_448 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_run'45'ir_448 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.RunAt.run-linked
d_run'45'linked_450 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'linked_450 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_444
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.RunAt.run-reach
d_run'45'reach_452 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_Reachable_364
d_run'45'reach_452 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_446
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.RunAt.run-tbl
d_run'45'tbl_454 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_run'45'tbl_454 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.+-not-<
d_'43''45'not'45''60'_462 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_462 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.AddrMap
d_AddrMap_464 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ExtDom
d_ExtDom_468 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr
d_FlatCorr_470 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.GapNext
d_GapNext_474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_GapNext_474 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HDom
d_HDom_476 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_476 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView
d_HeapView_478 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Memory
d_Memory_482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Memory_482 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.RetAddrs
d_RetAddrs_484 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer] -> ()
d_RetAddrs_484 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Sets2Roles
d_Sets2Roles_486 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                 a15 a16
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsMem
d_SetsMem_490 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRole
d_SetsRole_494 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRoleMem
d_SetsRoleMem_498 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                  a15 a16
  = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.StackWindows
d_StackWindows_502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_502 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Window
d_Window_504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny -> Integer -> ()
d_Window_504 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Word
d_Word_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_Word_506 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.amap
d_amap_508 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524
d_amap_508 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkAddrMap_534
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.at-addr
d_at'45'addr_510 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_510 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.at-role
d_at'45'role_512 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_512 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.at-role₁
d_at'45'role'8321'_514 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_514 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.at-role₂
d_at'45'role'8322'_516 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_516 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.atstack-frame-inj
d_atstack'45'frame'45'inj_518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
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
d_atstack'45'frame'45'inj_518 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.atstack-slot-inj
d_atstack'45'slot'45'inj_520 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_520 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.caddr
d_caddr_522 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_522 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.clos-eq
d_clos'45'eq_524 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_524 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.cmap
d_cmap_526 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_526 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_cmap_532
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.corr-regs-agree
d_corr'45'regs'45'agree_528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_corr'45'regs'45'agree_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_corr'45'regs'45'agree_528
du_corr'45'regs'45'agree_528 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_corr'45'regs'45'agree_528 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_corr'45'regs'45'agree_4868
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.corr-store-gap
d_corr'45'store'45'gap_530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_corr'45'store'45'gap_530 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_corr'45'store'45'gap_530 v1 v2
du_corr'45'store'45'gap_530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_corr'45'store'45'gap_530 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_corr'45'store'45'gap_4916
      (coe v0) (coe v1) v3 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.count-eq
d_count'45'eq_532 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_532 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.dec-enc
d_dec'45'enc_534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_534 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.descend-view
d_descend'45'view_536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
d_descend'45'view_536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_descend'45'view_536
du_descend'45'view_536 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
du_descend'45'view_536 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1630
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.dom-below
d_dom'45'below_538 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_538 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.dom-fresh
d_dom'45'fresh_540 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_540 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'fresh_1152
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.dom-sized
d_dom'45'sized_542 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_542 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.dom-written
d_dom'45'written_544 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_544 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-ext
d_enc'45'ext_546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_546 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-ext-maybe
d_enc'45'ext'45'maybe_548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_548 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-maybe
d_enc'45'maybe_550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe_550 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enc'45'maybe_550 v1
du_enc'45'maybe_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe_550 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'maybe_580
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-maybe-at
d_enc'45'maybe'45'at_552 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe'45'at_552 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_enc'45'maybe'45'at_552 v1
du_enc'45'maybe'45'at_552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe'45'at_552 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'maybe'45'at_564
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-sv
d_enc'45'sv_554 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv_554 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enc'45'sv_554 v1
du_enc'45'sv_554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv_554 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'sv_576
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-sv-at
d_enc'45'sv'45'at_556 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv'45'at_556 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_enc'45'sv'45'at_556 v1
du_enc'45'sv'45'at_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv'45'at_556 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'sv'45'at_536
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.enc-zero
d_enc'45'zero_558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_558 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-addr
d_ext'45'addr_560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_560 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ext'45'addr_560 v2
du_ext'45'addr_560 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_560 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ext'45'addr_3964
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-addr-aux
d_ext'45'addr'45'aux_562 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_562 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_ext'45'addr'45'aux_562 v2
du_ext'45'addr'45'aux_562 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_562 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ext'45'addr'45'aux_3946
      (coe v0) v1 v2 v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-addr-base
d_ext'45'addr'45'base_564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_564 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-addr-fresh
d_ext'45'addr'45'fresh_566 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_566 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-addr-old
d_ext'45'addr'45'old_568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_568 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-suc
d_ext'45'suc_574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_574 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ext-suc-aux
d_ext'45'suc'45'aux_576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_576 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.extend-view
d_extend'45'view_578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
d_extend'45'view_578 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_extend'45'view_578 v2
du_extend'45'view_578 ::
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
du_extend'45'view_578 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_extend'45'view_4122
      (coe v0) v1 v2 v3 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.frames-of
d_frames'45'of_580 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_frames'45'of_580
du_frames'45'of_580 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_580
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_frames'45'of_584
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.front-lo
d_front'45'lo_582 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_582 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.frontier-eq
d_frontier'45'eq_584 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_584 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.haddr
d_haddr_586 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_586 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.haddr-inj
d_haddr'45'inj_588 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_588 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.haddr-suc
d_haddr'45'suc_590 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_590 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.halt-eq
d_halt'45'eq_592 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_592 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.heap-eq
d_heap'45'eq_594 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_594 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.hfront
d_hfront_596 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_hfront_596 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.hmap
d_hmap_598 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_598 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hmap_530
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.in1-eq
d_in1'45'eq_600 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_600 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.inc-enc
d_inc'45'enc_602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_602 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-clos
d_keep'45'clos_604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'clos_604 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-count
d_keep'45'count_606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'count_606 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-halt
d_keep'45'halt_608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'halt_608 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-heap
d_keep'45'heap_610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap_610 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-heap-reg
d_keep'45'heap'45'reg_612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap'45'reg_612 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-in1
d_keep'45'in1_614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in1_614 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-lo-le
d_keep'45'lo'45'le_616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_keep'45'lo'45'le_616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_keep'45'lo'45'le_616
du_keep'45'lo'45'le_616 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_keep'45'lo'45'le_616 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_keep'45'lo'45'le_1278
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-out
d_keep'45'out_618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'out_618 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-scratch
d_keep'45'scratch_620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'scratch_620 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-sp
d_keep'45'sp_622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'sp_622 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-stack
d_keep'45'stack_624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_keep'45'stack_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_keep'45'stack_624
du_keep'45'stack_624 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_keep'45'stack_624 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_keep'45'stack_1296
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keep-untouched
d_keep'45'untouched_626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'untouched_626 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keeps-halt
d_keeps'45'halt_628 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_628 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keeps-halt₂
d_keeps'45'halt'8322'_630 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_630 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keeps-mem
d_keeps'45'mem_632 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_632 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.keeps-mem₂
d_keeps'45'mem'8322'_634 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_634 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.lit-word
d_lit'45'word_636 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_lit'45'word_636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_lit'45'word_636 v11
du_lit'45'word_636 :: Integer -> Integer
du_lit'45'word_636 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.lo
d_lo_638 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_lo_638 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.lo-le
d_lo'45'le_640 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_640 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo'45'le_1168
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mem-halt
d_mem'45'halt_642 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_642 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mem-regs
d_mem'45'regs_644 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_644 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-clos
d_mkeep'45'clos_650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'clos_650 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-count
d_mkeep'45'count_652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'count_652 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-halt
d_mkeep'45'halt_654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'halt_654 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-heap-reg
d_mkeep'45'heap'45'reg_656 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'heap'45'reg_656 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-in1
d_mkeep'45'in1_658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in1_658 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-lo-le
d_mkeep'45'lo'45'le_660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mkeep'45'lo'45'le_660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_mkeep'45'lo'45'le_660
du_mkeep'45'lo'45'le_660 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mkeep'45'lo'45'le_660 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_mkeep'45'lo'45'le_1380
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-out
d_mkeep'45'out_662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'out_662 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-scratch
d_mkeep'45'scratch_664 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'scratch_664 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.mkeep-sp
d_mkeep'45'sp_666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'sp_666 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.nz⇒pos
d_nz'8658'pos_668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nz'8658'pos_668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_nz'8658'pos_668
du_nz'8658'pos_668 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nz'8658'pos_668 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_nz'8658'pos_58
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.off-addr
d_off'45'addr_670 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_670 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.off-role
d_off'45'role_672 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_672 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.off-roles
d_off'45'roles_674 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_674 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.out-eq
d_out'45'eq_676 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_676 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.read-write-hit
d_read'45'write'45'hit_678 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'hit_678 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.read-write-miss
d_read'45'write'45'miss_680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
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
d_read'45'write'45'miss_680 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.readMem
d_readMem_682 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_readMem_682
du_readMem_682 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
du_readMem_682
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_readMem_66
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-agree-above
d_ret'45'agree'45'above_684 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
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
d_ret'45'agree'45'above_684 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_ret'45'agree'45'above_684 v1 v2
du_ret'45'agree'45'above_684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
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
du_ret'45'agree'45'above_684 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'agree'45'above_4996
      (coe v0) (coe v1) v2 v8 v11 v12 v14 v15 v16
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-agree-nothing
d_ret'45'agree'45'nothing_686 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'nothing_686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_ret'45'agree'45'nothing_686
du_ret'45'agree'45'nothing_686 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'nothing_686 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'agree'45'nothing_5352
      v8 v9 v11 v12
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-head
d_ret'45'head_688 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
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
d_ret'45'head_688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'head_688
du_ret'45'head_688 ::
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
du_ret'45'head_688 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'head_990
      v3 v9 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-nil-frames
d_ret'45'nil'45'frames_690 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
d_ret'45'nil'45'frames_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_ret'45'nil'45'frames_690
du_ret'45'nil'45'frames_690 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
du_ret'45'nil'45'frames_690 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'nil'45'frames_5452
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-relink
d_ret'45'relink_692 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
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
d_ret'45'relink_692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'relink_692
du_ret'45'relink_692 ::
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
du_ret'45'relink_692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'relink_798
      v0 v3 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-relk
d_ret'45'relk_694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
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
d_ret'45'relk_694 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'relk_694 v1 v2
du_ret'45'relk_694 ::
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
du_ret'45'relk_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'relk_884
      (coe v0) (coe v1) v2 v6 v7 v8 v9 v10
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-spill
d_ret'45'spill_696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
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
d_ret'45'spill_696 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'spill_696 v1
du_ret'45'spill_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
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
du_ret'45'spill_696 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'spill_5506
      (coe v0) v11 v12 v13 v15
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-unlink
d_ret'45'unlink_698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
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
d_ret'45'unlink_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_ret'45'unlink_698
du_ret'45'unlink_698 ::
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
du_ret'45'unlink_698 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'unlink_712
      v0 v3 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.ret-write-in-frame
d_ret'45'write'45'in'45'frame_700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
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
d_ret'45'write'45'in'45'frame_700 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                  ~v9 ~v10
  = du_ret'45'write'45'in'45'frame_700 v1 v2
du_ret'45'write'45'in'45'frame_700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
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
du_ret'45'write'45'in'45'frame_700 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'write'45'in'45'frame_5182
      (coe v0) (coe v1) v2 v7 v9 v12 v13 v14 v15 v16 v17 v18 v19
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.rm-at-addr
d_rm'45'at'45'addr_702 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_702 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.rm-at-role
d_rm'45'at'45'role_704 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_704 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.rm-halt
d_rm'45'halt_706 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_706 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.rm-off-addr
d_rm'45'off'45'addr_708 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_708 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.rm-off-role
d_rm'45'off'45'role_710 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_710 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.scratch-eq
d_scratch'45'eq_712 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_712 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sep
d_sep_714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 = du_sep_714
du_sep_714 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_714 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sep_1620
      v0 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-alloc-heap
d_sim'45'alloc'45'heap_716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'alloc'45'heap_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_sim'45'alloc'45'heap_716
du_sim'45'alloc'45'heap_716 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'alloc'45'heap_716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'alloc'45'heap_4462
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-alloc-stack
d_sim'45'alloc'45'stack_718 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'alloc'45'stack_718 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_sim'45'alloc'45'stack_718 v1 v2
du_sim'45'alloc'45'stack_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'alloc'45'stack_718 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'alloc'45'stack_3344
      (coe v0) (coe v1) v3 v4 v7 v12
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-call-frame
d_sim'45'call'45'frame_720 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'call'45'frame_720 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10
  = du_sim'45'call'45'frame_720 v1 v2 v6 v9
du_sim'45'call'45'frame_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'call'45'frame_720 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'call'45'frame_3578
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
         (coe v3))
      v6 v7 v9 v13
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-dealloc-stack
d_sim'45'dealloc'45'stack_722 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'dealloc'45'stack_722 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
                              ~v10
  = du_sim'45'dealloc'45'stack_722 v1 v6 v9
du_sim'45'dealloc'45'stack_722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'dealloc'45'stack_722 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'dealloc'45'stack_3662
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
         (coe v2))
      v5 v6 v8
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-heap-base
d_sim'45'heap'45'base_724 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'heap'45'base_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10
  = du_sim'45'heap'45'base_724
du_sim'45'heap'45'base_724 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'heap'45'base_724 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'heap'45'base_1700
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-lea-slot
d_sim'45'lea'45'slot_726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'lea'45'slot_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_sim'45'lea'45'slot_726
du_sim'45'lea'45'slot_726 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'lea'45'slot_726 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'lea'45'slot_4590
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-code-addr
d_sim'45'load'45'code'45'addr_728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'code'45'addr_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_sim'45'load'45'code'45'addr_728
du_sim'45'load'45'code'45'addr_728 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'code'45'addr_728 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'code'45'addr_3818
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-const
d_sim'45'load'45'const_730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'const_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_sim'45'load'45'const_730
du_sim'45'load'45'const_730 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'const_730 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'const_3764
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-const-float
d_sim'45'load'45'const'45'float_732 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'const'45'float_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10
  = du_sim'45'load'45'const'45'float_732
du_sim'45'load'45'const'45'float_732 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'const'45'float_732 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'const'45'float_3790
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-from-slot
d_sim'45'load'45'from'45'slot_734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'from'45'slot_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_sim'45'load'45'from'45'slot_734
du_sim'45'load'45'from'45'slot_734 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'from'45'slot_734 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'from'45'slot_2016
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-indirect
d_sim'45'load'45'indirect_736 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_sim'45'load'45'indirect_736
du_sim'45'load'45'indirect_736 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect_736 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect_1962
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_738 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect'45'stack_738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'stack_738
du_sim'45'load'45'indirect'45'stack_738 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect'45'stack_738 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_4632
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect'45'suc_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'suc_740
du_sim'45'load'45'indirect'45'suc_740 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect'45'suc_740 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_1908
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_742 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect'45'suc'45'stack_742 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'load'45'indirect'45'suc'45'stack_742
du_sim'45'load'45'indirect'45'suc'45'stack_742 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect'45'suc'45'stack_742 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_4690
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_744 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'tag'45'lit_744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_sim'45'load'45'tag'45'lit_744
du_sim'45'load'45'tag'45'lit_744 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'tag'45'lit_744 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_1748
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-mov-to-input
d_sim'45'mov'45'to'45'input_746 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'mov'45'to'45'input_746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_sim'45'mov'45'to'45'input_746
du_sim'45'mov'45'to'45'input_746 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'mov'45'to'45'input_746 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'to'45'input_1724
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-mov-to-output
d_sim'45'mov'45'to'45'output_748 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'mov'45'to'45'output_748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_sim'45'mov'45'to'45'output_748
du_sim'45'mov'45'to'45'output_748 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'mov'45'to'45'output_748 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'to'45'output_1678
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-out-nz
d_sim'45'out'45'nz_750 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'out'45'nz_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'out'45'nz_750
du_sim'45'out'45'nz_750 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'out'45'nz_750 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'out'45'nz_1774
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'count'45'inc_752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_sim'45'reg'45'count'45'inc_752
du_sim'45'reg'45'count'45'inc_752 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'count'45'inc_752 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_3890
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'count'45'zero_754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10
  = du_sim'45'reg'45'count'45'zero_754
du_sim'45'reg'45'count'45'zero_754 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'count'45'zero_754 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_1846
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'dec_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'dec_756
du_sim'45'reg'45'scratch'45'dec_756 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'dec_756 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_3920
      v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'load'45'count_758 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'load'45'count_758
du_sim'45'reg'45'scratch'45'load'45'count_758 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'load'45'count_758 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_1868
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'one_760 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'one_760
du_sim'45'reg'45'scratch'45'one_760 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'one_760 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_1802
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'zero_762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10
  = du_sim'45'reg'45'scratch'45'zero_762
du_sim'45'reg'45'scratch'45'zero_762 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'zero_762 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_1824
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-restore-input
d_sim'45'restore'45'input_764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'restore'45'input_764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_sim'45'restore'45'input_764
du_sim'45'restore'45'input_764 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'restore'45'input_764 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'restore'45'input_2998
      v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-ret
d_sim'45'ret_766 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'ret_766 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10
  = du_sim'45'ret_766 v1 v2 v6 v9
du_sim'45'ret_766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'ret_766 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'ret_3710
      (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_rreg_288
         (coe v3))
      v5 v8 v9 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'save'45'closure'45'reg_768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10
  = du_sim'45'save'45'closure'45'reg_768
du_sim'45'save'45'closure'45'reg_768 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'save'45'closure'45'reg_768 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'save'45'closure'45'reg_3846
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-store-at-slot
d_sim'45'store'45'at'45'slot_770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'at'45'slot_770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_sim'45'store'45'at'45'slot_770
du_sim'45'store'45'at'45'slot_770 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'at'45'slot_770 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'at'45'slot_3290
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-store-indirect
d_sim'45'store'45'indirect_772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect_772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_sim'45'store'45'indirect_772
du_sim'45'store'45'indirect_772 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect_772 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect_2892
      v1 v2 v5 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect'45'stack_774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'stack_774
du_sim'45'store'45'indirect'45'stack_774 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect'45'stack_774 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_4746
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect'45'suc_776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'suc_776
du_sim'45'store'45'indirect'45'suc_776 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect'45'suc_776 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_2944
      v1 v2 v5 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect'45'suc'45'stack_778 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'store'45'indirect'45'suc'45'stack_778
du_sim'45'store'45'indirect'45'suc'45'stack_778 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect'45'suc'45'stack_778 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_4808
      v2 v5
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sim-thunk
d_sim'45'thunk_780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'thunk_780 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sim'45'thunk_780 v1 v2
du_sim'45'thunk_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'thunk_780 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'thunk_3446
      (coe v0) (coe v1) v3 v4 v7 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.slot-addr-inj
d_slot'45'addr'45'inj_782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_782 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.slot-size>0
d_slot'45'size'62'0_784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'size'62'0_784 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_slot'45'size'62'0_784
du_slot'45'size'62'0_784 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'size'62'0_784
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slot'45'size'62'0_60
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.slot-to-disp
d_slot'45'to'45'disp_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_slot'45'to'45'disp_786 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10
  = du_slot'45'to'45'disp_786 v2
du_slot'45'to'45'disp_786 :: Integer -> Integer -> Integer
du_slot'45'to'45'disp_786 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slot'45'to'45'disp_52
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.slots
d_slots_788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> Integer
d_slots_788 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_slots_788 v2
du_slots_788 :: Integer -> Integer -> Integer
du_slots_788 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sp-eq
d_sp'45'eq_790 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_790 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.stack-eq
d_stack'45'eq_792 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_792 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_stack'45'eq_1174
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.stack-eq-cur
d_stack'45'eq'45'cur_794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_794 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.stack-eq-win
d_stack'45'eq'45'win_796 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_796 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.store-dom-written
d_store'45'dom'45'written_798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_store'45'dom'45'written_798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10
  = du_store'45'dom'45'written_798
du_store'45'dom'45'written_798 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_798 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_store'45'dom'45'written_2292
      v1 v4 v5 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.store-heap-eq
d_store'45'heap'45'eq_800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_800 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_802 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_804 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.sv-tag-zero
d_sv'45'tag'45'zero_806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_806 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.untouched
d_untouched_808 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_808 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.untouched-descend
d_untouched'45'descend_810 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_810 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.untouched-heap-store
d_untouched'45'heap'45'store_812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_812 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.untouched-stack-store
d_untouched'45'stack'45'store_814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_814 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.untouched-write
d_untouched'45'write_816 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_816 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.win-at
d_win'45'at_818 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_818 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.win-off
d_win'45'off_820 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_820 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.window-store-above
d_window'45'store'45'above_822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_window'45'store'45'above_822 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-above
d_windows'45'above_824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'above_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_windows'45'above_824
du_windows'45'above_824 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'above_824 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'above_2602
      v6 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-enc-ext
d_windows'45'enc'45'ext_826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_windows'45'enc'45'ext_826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_windows'45'enc'45'ext_826
du_windows'45'enc'45'ext_826 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_826 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'enc'45'ext_4380
      v8 v10
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-forget
d_windows'45'forget_828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'forget_828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_windows'45'forget_828
du_windows'45'forget_828 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'forget_828 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'forget_2482
      v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-heap-store
d_windows'45'heap'45'store_830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_windows'45'heap'45'store_830
du_windows'45'heap'45'store_830 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_830 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'heap'45'store_2864
      v1 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-leave
d_windows'45'leave_832 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_832 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_windows'45'leave_832 v1
du_windows'45'leave_832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_832 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'leave_2536
      (coe v0) v4 v6
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-lower
d_windows'45'lower_834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'lower_834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_windows'45'lower_834
du_windows'45'lower_834 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'lower_834 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'lower_2436
      v5 v6 v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-reanchor
d_windows'45'reanchor_836 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'reanchor_836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10
  = du_windows'45'reanchor_836
du_windows'45'reanchor_836 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_836 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'reanchor_2406
      v8 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-slot-store
d_windows'45'slot'45'store_838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10
  = du_windows'45'slot'45'store_838
du_windows'45'slot'45'store_838 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_838 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'slot'45'store_3218
      v9 v12
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-store-gap
d_windows'45'store'45'gap_840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'store'45'gap_840 ~v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                              ~v10
  = du_windows'45'store'45'gap_840 v1 v2
du_windows'45'store'45'gap_840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'store'45'gap_840 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'store'45'gap_2726
      (coe v0) (coe v1) v7 v8 v9 v11
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.windows-write-below
d_windows'45'write'45'below_842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10
  = du_windows'45'write'45'below_842
du_windows'45'write'45'below_842 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_842 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'write'45'below_2816
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.writeMem
d_writeMem_844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_writeMem_844
du_writeMem_844 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
du_writeMem_844
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_writeMem_72
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.≡ᵇ-refl
d_'8801''7495''45'refl_846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_846 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_848 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.AddrMap.cmap
d_cmap_852 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_852 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_cmap_532
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.AddrMap.hmap
d_hmap_854 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_854 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hmap_530
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.clos-eq
d_clos'45'eq_864 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_864 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.count-eq
d_count'45'eq_866 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_866 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.dom-fresh
d_dom'45'fresh_868 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_868 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'fresh_1152
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.dom-sized
d_dom'45'sized_870 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_870 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.dom-written
d_dom'45'written_872 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_872 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.frontier-eq
d_frontier'45'eq_874 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_874 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.halt-eq
d_halt'45'eq_876 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_876 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.heap-eq
d_heap'45'eq_878 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_878 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.in1-eq
d_in1'45'eq_880 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_880 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.lo-le
d_lo'45'le_882 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_882 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo'45'le_1168
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.out-eq
d_out'45'eq_884 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_884 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.scratch-eq
d_scratch'45'eq_886 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_886 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.sp-eq
d_sp'45'eq_888 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_888 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.stack-eq
d_stack'45'eq_890 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_890 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_stack'45'eq_1174
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.FlatCorr.untouched
d_untouched_892 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_892 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.HDom
d_HDom_896 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_896 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.caddr
d_caddr_898 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_898 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.dom-below
d_dom'45'below_900 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_900 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.front-lo
d_front'45'lo_902 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_902 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.haddr
d_haddr_904 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_904 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.haddr-inj
d_haddr'45'inj_906 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_906 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.haddr-suc
d_haddr'45'suc_908 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_908 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.hfront
d_hfront_910 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_hfront_910 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.HeapView.lo
d_lo_912 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_lo_912 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Sets2Roles.at-role₁
d_at'45'role'8321'_916 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_916 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Sets2Roles.at-role₂
d_at'45'role'8322'_918 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_918 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Sets2Roles.keeps-halt₂
d_keeps'45'halt'8322'_920 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_920 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Sets2Roles.keeps-mem₂
d_keeps'45'mem'8322'_922 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_922 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.Sets2Roles.off-roles
d_off'45'roles_924 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_924 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsMem.at-addr
d_at'45'addr_928 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_928 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsMem.mem-halt
d_mem'45'halt_930 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_930 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsMem.mem-regs
d_mem'45'regs_932 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_932 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsMem.off-addr
d_off'45'addr_934 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_934 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRole.at-role
d_at'45'role_938 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_938 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRole.keeps-halt
d_keeps'45'halt_940 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_940 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRole.keeps-mem
d_keeps'45'mem_942 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_942 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRole.off-role
d_off'45'role_944 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_944 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRoleMem.rm-at-addr
d_rm'45'at'45'addr_948 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_948 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRoleMem.rm-at-role
d_rm'45'at'45'role_950 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_950 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRoleMem.rm-halt
d_rm'45'halt_952 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_952 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRoleMem.rm-off-addr
d_rm'45'off'45'addr_954 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_954 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.CFC.SetsRoleMem.rm-off-role
d_rm'45'off'45'role_956 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_956 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.count-reg
d_count'45'reg_960 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_count'45'reg_960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_count'45'reg_960 v6
du_count'45'reg_960 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_count'45'reg_960 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_count'45'reg_48
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.in1-reg
d_in1'45'reg_962 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_in1'45'reg_962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_in1'45'reg_962 v6
du_in1'45'reg_962 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_in1'45'reg_962 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_44
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.scratch-reg
d_scratch'45'reg_966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_scratch'45'reg_966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_scratch'45'reg_966 v6
du_scratch'45'reg_966 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_scratch'45'reg_966 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_46
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.sp-reg
d_sp'45'reg_968 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  AgdaAny
d_sp'45'reg_968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_sp'45'reg_968 v6
du_sp'45'reg_968 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_sp'45'reg_968 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.ArithEnv
d_ArithEnv_972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_ArithEnv_972 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.EvExtractor
d_EvExtractor_974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  ()
d_EvExtractor_974 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events
d_run'45'events_976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events_976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_run'45'events_976 v8 v9 v10
du_run'45'events_976 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events_976 v0 v1 v2
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-[]
d_run'45'events'45''91''93'_978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  (Integer ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45''91''93'_978 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-arith
d_run'45'events'45'arith_980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
d_run'45'events'45'arith_980 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-call
d_run'45'events'45'call_982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events'45'call_982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                            v10
  = du_run'45'events'45'call_982 v8 v9 v10
du_run'45'events'45'call_982 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'call_982 v0 v1 v2
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-exec
d_run'45'events'45'exec_984 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events'45'exec_984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                            v10
  = du_run'45'events'45'exec_984 v8 v9 v10
du_run'45'events'45'exec_984 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'exec_984 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
      v3 v4 v5 v6 v7 v9
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-external
d_run'45'events'45'external_986 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
d_run'45'events'45'external_986 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-fetch
d_run'45'events'45'fetch_988 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events'45'fetch_988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                             v10
  = du_run'45'events'45'fetch_988 v8 v9 v10
du_run'45'events'45'fetch_988 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'fetch_988 v0 v1 v2
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-fetch-none
d_run'45'events'45'fetch'45'none_990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'fetch'45'none_990 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-halted
d_run'45'events'45'halted_992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'halted_992 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-instr
d_run'45'events'45'instr_994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'events'45'instr_994 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                             v10
  = du_run'45'events'45'instr_994 v8 v9 v10
du_run'45'events'45'instr_994 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'events'45'instr_994 v0 v1 v2
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-noncall
d_run'45'events'45'noncall_996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
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
d_run'45'events'45'noncall_996 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-events-stuck
d_run'45'events'45'stuck_998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'events'45'stuck_998 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-trace
d_run'45'trace_1000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'trace_1000 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_run'45'trace_1000 v8 v9 v10
du_run'45'trace_1000 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_run'45'trace_1000 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace_228
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-trace-extends
d_run'45'trace'45'extends_1002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'trace'45'extends_1002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                               v9 v10
  = du_run'45'trace'45'extends_1002 v8 v9 v10
du_run'45'trace'45'extends_1002 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'trace'45'extends_1002 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.d_run'45'trace'45'extends_210
      erased erased erased erased
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xhalted_292
         (coe v1))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_xpc_294
         (coe v1))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mfetch_118
         (coe v0))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_mexecInstr_298
         (coe v1))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_matchCall_438
         (coe v2))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-trace-fam
d_run'45'trace'45'fam_1004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_run'45'trace'45'fam_1004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                           v10
  = du_run'45'trace'45'fam_1004 v8 v9 v10
du_run'45'trace'45'fam_1004 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_run'45'trace'45'fam_1004 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Arith.Backend.RunTraceCore.du_run'45'trace'45'fam_182
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
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_ret'45'call_440
         (coe v2))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.d_dispatchArith_442
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.RT.run-trace-saturates
d_run'45'trace'45'saturates_1006 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (Integer -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_run'45'trace'45'saturates_1006 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState
d_FlatState_1010 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.fetch
d_fetch_1018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
d_fetch_1018 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_fetch_1018
du_fetch_1018 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250
du_fetch_1018 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.flat-exec-instr
d_flat'45'exec'45'instr_1020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_1020 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10
  = du_flat'45'exec'45'instr_1020 v1
du_flat'45'exec'45'instr_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_1020 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1502
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState.falloc
d_falloc_1028 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_falloc_1028 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState.fclosure
d_fclosure_1030 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_1030 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState.flink
d_flink_1032 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_1032 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState.floc
d_floc_1034 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_floc_1034 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState.fpc
d_fpc_1036 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_1036 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatState.fret
d_fret_1038 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_1038 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.readLoc
d_readLoc_1042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_readLoc_1042
du_readLoc_1042 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1042
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatWF
d_FlatWF_1046 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatWF_1046 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.sv-below
d_sv'45'below_1052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_1052 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.FlatRegTag
d_FlatRegTag_1056 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> ()
d_FlatRegTag_1056 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv
d_FlatInv_1068 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  = ()
data T_FlatInv_1068
  = C_mkFlatInv_1106 MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
                     AgdaAny MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_528
                     AgdaAny
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-wf
d_inv'45'wf_1092 ::
  T_FlatInv_1068 ->
  MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.T_StoreWF_736
d_inv'45'wf_1092 v0
  = case coe v0 of
      C_mkFlatInv_1106 v1 v2 v3 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-closure
d_inv'45'closure_1094 :: T_FlatInv_1068 -> AgdaAny
d_inv'45'closure_1094 v0
  = case coe v0 of
      C_mkFlatInv_1106 v1 v2 v3 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-regtag
d_inv'45'regtag_1096 ::
  T_FlatInv_1068 ->
  MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.T_RegTagWF_528
d_inv'45'regtag_1096 v0
  = case coe v0 of
      C_mkFlatInv_1106 v1 v2 v3 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-ev
d_inv'45'ev_1098 ::
  T_FlatInv_1068 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv'45'ev_1098 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-env
d_inv'45'env_1100 :: T_FlatInv_1068 -> AgdaAny
d_inv'45'env_1100 v0
  = case coe v0 of
      C_mkFlatInv_1106 v1 v2 v3 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-run
d_inv'45'run_1102 ::
  T_FlatInv_1068 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422
d_inv'45'run_1102 v0
  = case coe v0 of
      C_mkFlatInv_1106 v1 v2 v3 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.FlatInv.inv-started
d_inv'45'started_1104 ::
  T_FlatInv_1068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_inv'45'started_1104 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.flat-inv-step
d_flat'45'inv'45'step_1118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FlatInv_1068 -> T_FlatInv_1068
d_flat'45'inv'45'step_1118 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 v13 v14 v15 ~v16 ~v17 v18
  = du_flat'45'inv'45'step_1118 v1 v13 v14 v15 v18
du_flat'45'inv'45'step_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatInv_1068 -> T_FlatInv_1068
du_flat'45'inv'45'step_1118 v0 v1 v2 v3 v4
  = coe
      C_mkFlatInv_1106
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_flat'45'wf'45'step_2846
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_inv'45'wf_1092 (coe v4)))
      (MAlonzo.Code.Once.CCC.Machine.FlatStoreWF.d_cl'45'step_2466
         (coe v0) (coe v1) (coe v2) (coe v3) (coe d_inv'45'wf_1092 (coe v4))
         (coe d_inv'45'closure_1094 (coe v4)))
      (MAlonzo.Code.Once.CCC.Machine.FlatRegTagWF.d_flat'45'regtag'45'step_1646
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_inv'45'regtag_1096 (coe v4)))
      (d_inv'45'env_1100 (coe v4))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_mkRunAt_448
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'tbl_438
            (coe d_inv'45'run_1102 (coe v4)))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'ir_440
            (coe d_inv'45'run_1102 (coe v4)))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'linked_444
            (coe d_inv'45'run_1102 (coe v4)))
         (coe
            MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.C_reach'45'step_378
            v1 v3
            (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.d_run'45'reach_446
               (coe d_inv'45'run_1102 (coe v4)))))
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.t≢f
d_t'8802'f_1132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_t'8802'f_1132 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.n≢j
d_n'8802'j_1138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_1138 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.block-run-exec
d_block'45'run'45'exec_1156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'run'45'exec_1156 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.go-h
d_go'45'h_1200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'h_1200 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._._.go-f
d_go'45'f_1212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'f_1212 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._._._.go-e
d_go'45'e_1226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'e_1226 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._._._._.go-h1
d_go'45'h1_1240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'h1_1240 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.event-of
d_event'45'of_1248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_event'45'of_1248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_event'45'of_1248
du_event'45'of_1248 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_event'45'of_1248
  = coe MAlonzo.Code.Once.Adequacy.FlatEvents.du_event'45'of_458
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.flat-events
d_flat'45'events_1250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_flat'45'events_1250 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_flat'45'events_1250 v1
du_flat'45'events_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_flat'45'events_1250 v0
  = coe
      MAlonzo.Code.Once.Adequacy.FlatEvents.d_flat'45'events_464 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.events-running-end
d_events'45'running'45'end_1276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  T_FlatInv_1068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'45'running'45'end_1276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
                                ~v22
  = du_events'45'running'45'end_1276
du_events'45'running'45'end_1276 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'45'running'45'end_1276
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
      erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine._.cfetch-nothing
d_cfetch'45'nothing_1306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  T_FlatInv_1068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cfetch'45'nothing_1306 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.sigop-concrete-fetch
d_sigop'45'concrete'45'fetch_1328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'concrete'45'fetch_1328 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.sigop-run-arith
d_sigop'45'run'45'arith_1374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'run'45'arith_1374 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.sigop-run-external
d_sigop'45'run'45'external_1424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'run'45'external_1424 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.event-of-pure
d_event'45'of'45'pure_1458 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_event'45'of'45'pure_1458 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckAt
d_StuckAt_1470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [AgdaAny] -> AgdaAny -> ()
d_StuckAt_1470 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckSteps
d_StuckSteps_1484 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_StuckSteps_1484
  = C_constructor_1650 (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         AgdaAny ->
                         [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        AgdaAny ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         AgdaAny ->
                         [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        AgdaAny ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         AgdaAny ->
                         [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         AgdaAny ->
                         [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         AgdaAny ->
                         [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckSteps.st-load-indirect
d_st'45'load'45'indirect_1582 ::
  T_StuckSteps_1484 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'load'45'indirect_1582 v0
  = case coe v0 of
      C_constructor_1650 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckSteps.st-load-indirect-suc
d_st'45'load'45'indirect'45'suc_1598 ::
  T_StuckSteps_1484 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'load'45'indirect'45'suc_1598 v0
  = case coe v0 of
      C_constructor_1650 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckSteps.st-c-jmp
d_st'45'c'45'jmp_1614 ::
  T_StuckSteps_1484 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'jmp_1614 v0
  = case coe v0 of
      C_constructor_1650 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckSteps.st-c-branch-scratch-zero
d_st'45'c'45'branch'45'scratch'45'zero_1630 ::
  T_StuckSteps_1484 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'branch'45'scratch'45'zero_1630 v0
  = case coe v0 of
      C_constructor_1650 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.StuckSteps.st-c-branch-tag-zero
d_st'45'c'45'branch'45'tag'45'zero_1648 ::
  T_StuckSteps_1484 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_st'45'c'45'branch'45'tag'45'zero_1648 v0
  = case coe v0 of
      C_constructor_1650 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.stuck-result
d_stuck'45'result_1670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Emitter_14 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_Machine_196 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.EngineInterface.T_TraceLoop_366 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stuck'45'result_1670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_stuck'45'result_1670 v13 v21
du_stuck'45'result_1670 ::
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
  ([MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124] ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stuck'45'result_1670 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1 v0)) erased
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply
d_Supply_1696 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Supply_1696
  = C_constructor_2042 MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886
                       T_StuckSteps_1484
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        Integer ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                       (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         AgdaAny ->
                         [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
                        (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
                        [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
                        MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        AgdaAny ->
                        MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.bss
d_bss_1870 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_BlockSteps_886
d_bss_1870 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.sts
d_sts_1872 :: T_Supply_1696 -> T_StuckSteps_1484
d_sts_1872 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.heap-room
d_heap'45'room_1884 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'room_1884 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.stack-room
d_stack'45'room_1898 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_stack'45'room_1898 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.call-room
d_call'45'room_1910 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_call'45'room_1910 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.reg-range
d_reg'45'range_1922 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reg'45'range_1922 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.scratch-dec-guarded
d_scratch'45'dec'45'guarded_1932 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'dec'45'guarded_1932 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.ret-no-wrap
d_ret'45'no'45'wrap_1944 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ret'45'no'45'wrap_1944 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.count-no-wrap
d_count'45'no'45'wrap_1954 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_count'45'no'45'wrap_1954 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.tag-fits
d_tag'45'fits_1966 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tag'45'fits_1966 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.lit-fits
d_lit'45'fits_1978 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lit'45'fits_1978 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.float-fits
d_float'45'fits_1990 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_float'45'fits_1990 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.lo-fits
d_lo'45'fits_2000 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'fits_2000 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.arith-sigop-contract
d_arith'45'sigop'45'contract_2020 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  AgdaAny ->
  MAlonzo.Code.Once.SigOp.Info.T_Internal_360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arith'45'sigop'45'contract_2020 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine.Supply.external-sigop-contract
d_external'45'sigop'45'contract_2040 ::
  T_Supply_1696 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RunContext.T_RunAt_422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.SigOp.Info.T_External_378 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence.T_CompiledCorr_672 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_external'45'sigop'45'contract_2040 v0
  = case coe v0 of
      C_constructor_2042 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
