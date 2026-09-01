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

module MAlonzo.Code.Once.CCC.Codegen.CataIRSlotStable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.CataIRSlotStable._.CataStrategy
d_CataStrategy_12 a0 = ()
-- Once.CCC.Codegen.CataIRSlotStable._.cata-body
d_cata'45'body_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'body_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'body_90 (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-br-I₁
d_cata'45'br'45'I'8321'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'br'45'I'8321'_16 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-dispatch
d_cata'45'dispatch_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-branching
d_cata'45'trace'45'branching_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_40 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'branching_340
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-const
d_cata'45'trace'45'const_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'const_42 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'const_352
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-linear
d_cata'45'trace'45'linear_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'linear_44 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'linear_146
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-nat
d_cata'45'trace'45'nat_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'nat_46 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'nat_120
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.ir-to-trace
d_ir'45'to'45'trace_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_50 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_738
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.ir-to-trace'
d_ir'45'to'45'trace''_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_52 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.rebuild-walk
d_rebuild'45'walk_56 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_rebuild'45'walk_56 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.CataIRSlotStable._.visit-walk
d_visit'45'walk_66 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_visit'45'walk_66 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.AllSlotStable
d_AllSlotStable_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_AllSlotStable_84 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.SlotStable
d_SlotStable_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> ()
d_SlotStable_86 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.SlotStableT
d_SlotStableT_88 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_SlotStableT_88 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.trc
d_trc_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trc_94 ~v0 ~v1 v2 = du_trc_94 v2
du_trc_94 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_trc_94 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.All→AllI
d_All'8594'AllI_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_100 ~v0 ~v1 v2 v3 = du_All'8594'AllI_100 v2 v3
du_All'8594'AllI_100 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe du_All'8594'AllI_100 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?
d_stable'63'_106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 -> Bool
d_stable'63'_106 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2240 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2244 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_all'45'stable'63'_108 (coe v0) (coe v1) (coe v4))
                (coe d_all'45'stable'63'_108 (coe v0) (coe v1) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2282 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> coe v3)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?
d_all'45'stable'63'_108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> Bool
d_all'45'stable'63'_108 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_stable'63'_106 (coe v0) (coe v1) (coe v3))
             (coe d_all'45'stable'63'_108 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.∧-split
d_'8743''45'split_122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_122 ~v0 ~v1 v2 v3 ~v4
  = du_'8743''45'split_122 v2 v3
du_'8743''45'split_122 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_122 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_126 v0 v1 v2 ~v3
  = du_stable'63''45'sound_126 v0 v1 v2
du_stable'63''45'sound_126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny
du_stable'63''45'sound_126 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2236 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2242 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2246 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2248
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2250
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2252 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2254 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2256 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2258 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2264 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2270 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2272 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2274
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2278 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_All'8594'AllI_100 (coe v3)
                (coe du_all'45'stable'63''45'sound_130 (coe v0) (coe v1) (coe v3)))
             (coe
                du_All'8594'AllI_100 (coe v4)
                (coe du_all'45'stable'63''45'sound_130 (coe v0) (coe v1) (coe v4)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2288 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_130 v0 v1 v2 ~v3
  = du_all'45'stable'63''45'sound_130 v0 v1 v2
du_all'45'stable'63''45'sound_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'stable'63''45'sound_130 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_stable'63''45'sound_126 (coe v0) (coe v1) (coe v3))
             (coe du_all'45'stable'63''45'sound_130 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.AllI→All
d_AllI'8594'All_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_154 ~v0 ~v1 v2 v3 = du_AllI'8594'All_154 v2 v3
du_AllI'8594'All_154 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_154 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                    (coe du_AllI'8594'All_154 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.∧-intro
d_'8743''45'intro_164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_164 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_180 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_180 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_194 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_198 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_228 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Once.Type.C_K_110 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      MAlonzo.Code.Once.Type.C__'8853'__114 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                         (coe v0) (coe v2) (coe v3) (coe v4) (coe v9)
                         (coe addInt (coe (4 :: Integer)) (coe v6))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v8)))
                            (coe v7)))
                      (coe
                         d_visit'45'walk'45'stable_228 (coe v0) (coe v1) (coe v2) (coe v3)
                         (coe v4) (coe v9) (coe addInt (coe (4 :: Integer)) (coe v6))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v8)))
                            (coe v7)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                                        (coe v0) (coe v2) (coe v3) (coe v4) (coe v8)
                                        (coe addInt (coe (4 :: Integer)) (coe v6))
                                        (coe addInt (coe (2 :: Integer)) (coe v7)))
                                     (coe
                                        d_visit'45'walk'45'stable_228 (coe v0) (coe v1) (coe v2)
                                        (coe v3) (coe v4) (coe v8)
                                        (coe addInt (coe (4 :: Integer)) (coe v6))
                                        (coe addInt (coe (2 :: Integer)) (coe v7)))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
      MAlonzo.Code.Once.Type.C__'8855'__116 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                            (coe v0) (coe v2) (coe v3) (coe v4) (coe v9)
                            (coe addInt (coe (4 :: Integer)) (coe v6))
                            (coe
                               addInt
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v8))
                               (coe v7)))
                         (coe
                            d_visit'45'walk'45'stable_228 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v9) (coe addInt (coe (4 :: Integer)) (coe v6))
                            (coe
                               addInt
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v8))
                               (coe v7)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (d_visit'45'walk'45'stable_228
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                                     (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7)))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_290 v0 v1 v2 ~v3 ~v4 v5 v6 v7
  = du_rebuild'45'walk'45'stable_290 v0 v1 v2 v5 v6 v7
du_rebuild'45'walk'45'stable_290 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'stable_290 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_K_110 v6
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Type.C__'8853'__114 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                         (coe v0) (coe v2) (coe v7)
                         (coe addInt (coe (4 :: Integer)) (coe v4))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v6)))
                            (coe v5)))
                      (coe
                         du_rebuild'45'walk'45'stable_290 (coe v0) (coe v1) (coe v2)
                         (coe v7) (coe addInt (coe (4 :: Integer)) (coe v4))
                         (coe
                            addInt
                            (coe
                               addInt (coe (2 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v6)))
                            (coe v5)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                    (coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          (coe
                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             (coe
                                                                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                                                                   (coe v0) (coe v2) (coe v6)
                                                                   (coe
                                                                      addInt (coe (4 :: Integer))
                                                                      (coe v4))
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v5)))
                                                                (coe
                                                                   du_rebuild'45'walk'45'stable_290
                                                                   (coe v0) (coe v1) (coe v2)
                                                                   (coe v6)
                                                                   (coe
                                                                      addInt (coe (4 :: Integer))
                                                                      (coe v4))
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v5)))
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                         (coe
                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                            (coe
                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))))
      MAlonzo.Code.Once.Type.C__'8855'__116 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                            (coe v0) (coe v2) (coe v6)
                            (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                         (coe
                            du_rebuild'45'walk'45'stable_290 (coe v0) (coe v1) (coe v2)
                            (coe v6) (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                        (coe
                                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                                           (coe v0) (coe v2) (coe v7)
                                           (coe addInt (coe (4 :: Integer)) (coe v4))
                                           (coe
                                              addInt
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                                 (coe v6))
                                              (coe v5)))
                                        (coe
                                           du_rebuild'45'walk'45'stable_290 (coe v0) (coe v1)
                                           (coe v2) (coe v7)
                                           (coe addInt (coe (4 :: Integer)) (coe v4))
                                           (coe
                                              addInt
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                                 (coe v6))
                                              (coe v5)))
                                        (coe
                                           du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                 (coe addInt (coe (2 :: Integer)) (coe v4)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                    (coe (2 :: Integer)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                       (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v4)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v4)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                         (coe
                                                                            addInt
                                                                            (coe (3 :: Integer))
                                                                            (coe v4)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-body-stable
d_cata'45'body'45'stable_348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'stable_348 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_cata'45'body'45'stable_348 v5 v6
du_cata'45'body'45'stable_348 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'stable_348 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-const-stable
d_cata'45'trace'45'const'45'stable_368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'const'45'stable_368 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'trace'45'const'45'stable_368 v0 v1 v3 v4 v5 v6
du_cata'45'trace'45'const'45'stable_368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'const'45'stable_368 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
            (coe v0) (coe v2) (coe addInt (coe (1 :: Integer)) (coe v2))
            (coe addInt (coe (2 :: Integer)) (coe v2))
            (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
            (coe v2) (coe addInt (coe (1 :: Integer)) (coe v2))
            (coe addInt (coe (3 :: Integer)) (coe v2))))
      (coe
         du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
               (coe v0) (coe v2) (coe addInt (coe (1 :: Integer)) (coe v2))
               (coe addInt (coe (2 :: Integer)) (coe v2))
               (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
               (coe v2) (coe addInt (coe (1 :: Integer)) (coe v2))
               (coe addInt (coe (3 :: Integer)) (coe v2)))))
      (coe du_cata'45'body'45'stable_348 (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_388 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'trace'45'nat'45'stable_388 v0 v1 v3 v4 v5 v6
du_cata'45'trace'45'nat'45'stable_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'nat'45'stable_388 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
            (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2))
            (coe addInt (coe (3 :: Integer)) (coe v2))
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2))
            (coe addInt (coe (6 :: Integer)) (coe v3)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8321'_74
               (coe v0) (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                  (coe addInt (coe (2 :: Integer)) (coe v2))
                  (coe addInt (coe (3 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8322'_80
                     (coe v0) (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                        (coe addInt (coe (2 :: Integer)) (coe v2))
                        (coe addInt (coe (3 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8323'_86
                        (coe v0) (coe v3)))))))
      (coe
         du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
               (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2))
               (coe addInt (coe (3 :: Integer)) (coe v2))
               (coe addInt (coe (4 :: Integer)) (coe v2))
               (coe addInt (coe (5 :: Integer)) (coe v2))
               (coe addInt (coe (6 :: Integer)) (coe v3)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8321'_74
                  (coe v0) (coe v2) (coe v3))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                     (coe addInt (coe (2 :: Integer)) (coe v2))
                     (coe addInt (coe (3 :: Integer)) (coe v2))
                     (coe addInt (coe (5 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8322'_80
                        (coe v0) (coe v2) (coe v3))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                           (coe addInt (coe (2 :: Integer)) (coe v2))
                           (coe addInt (coe (3 :: Integer)) (coe v2))
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8323'_86
                           (coe v0) (coe v3))))))))
      (coe du_cata'45'body'45'stable_348 (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_408 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'trace'45'linear'45'stable_408 v0 v1 v3 v4 v5 v6
du_cata'45'trace'45'linear'45'stable_408 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'linear'45'stable_408 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
            (coe v0) (coe addInt (coe (6 :: Integer)) (coe v2))
            (coe addInt (coe (7 :: Integer)) (coe v2))
            (coe addInt (coe (8 :: Integer)) (coe v2))
            (coe addInt (coe (9 :: Integer)) (coe v2))
            (coe addInt (coe (4 :: Integer)) (coe v3)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8321'_130
               (coe v0) (coe v2) (coe v3))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                  (coe addInt (coe (6 :: Integer)) (coe v2))
                  (coe addInt (coe (7 :: Integer)) (coe v2))
                  (coe addInt (coe (9 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8322'_136
                     (coe v0) (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                        (coe addInt (coe (6 :: Integer)) (coe v2))
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (9 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8323'_142
                        (coe v0) (coe v3)))))))
      (coe
         du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
               (coe v0) (coe addInt (coe (6 :: Integer)) (coe v2))
               (coe addInt (coe (7 :: Integer)) (coe v2))
               (coe addInt (coe (8 :: Integer)) (coe v2))
               (coe addInt (coe (9 :: Integer)) (coe v2))
               (coe addInt (coe (4 :: Integer)) (coe v3)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8321'_130
                  (coe v0) (coe v2) (coe v3))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                     (coe addInt (coe (6 :: Integer)) (coe v2))
                     (coe addInt (coe (7 :: Integer)) (coe v2))
                     (coe addInt (coe (9 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8322'_136
                        (coe v0) (coe v2) (coe v3))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                           (coe addInt (coe (6 :: Integer)) (coe v2))
                           (coe addInt (coe (7 :: Integer)) (coe v2))
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'lin'45'I'8323'_142
                           (coe v0) (coe v3))))))))
      (coe du_cata'45'body'45'stable_348 (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_430 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_cata'45'trace'45'branching'45'stable_430 v0 v1 v2 v4 v5 v6 v7
du_cata'45'trace'45'branching'45'stable_430 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'branching'45'stable_430 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
         (coe v0) (coe du_cl_450 (coe v2) (coe v3))
         (coe addInt (coe (1 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
         (coe addInt (coe (2 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
         (coe addInt (coe (3 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
         (coe du_bodyL_448 (coe v2) (coe v4)))
      (coe
         du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
            (coe v0) (coe du_cl_450 (coe v2) (coe v3))
            (coe addInt (coe (1 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
            (coe addInt (coe (2 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
            (coe addInt (coe (3 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
            (coe du_bodyL_448 (coe v2) (coe v4))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
            (coe v0) (coe v2) (coe v3) (coe v4))
         (coe
            du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
               (coe v0) (coe v2) (coe v3) (coe v4)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
               (coe du_cl_450 (coe v2) (coe v3))
               (coe addInt (coe (1 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
               (coe
                  addInt (coe (3 :: Integer)) (coe du_cl_450 (coe v2) (coe v3))))
            (coe
               du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                  (coe du_cl_450 (coe v2) (coe v3))
                  (coe addInt (coe (1 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))
                  (coe
                     addInt (coe (3 :: Integer)) (coe du_cl_450 (coe v2) (coe v3)))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                  (coe v0) (coe v3) (coe v4))
               (coe
                  du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                     (coe v0) (coe v3) (coe v4)))
               (coe du_cata'45'body'45'stable_348 (coe v5) (coe v6)))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.bodyL
d_bodyL_448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_bodyL_448 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 = du_bodyL_448 v2 v5
du_bodyL_448 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_bodyL_448 v0 v1
  = coe
      addInt
      (coe
         addInt
         (coe
            addInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v0)))
      (coe v1)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.cl
d_cl_450 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_cl_450 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 = du_cl_450 v2 v4
du_cl_450 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_cl_450 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (11 :: Integer))
         (coe
            mulInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_156 (coe v0))))
      (coe v1)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.I₁-true
d_I'8321''45'true_452 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'true_452 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_464 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_cata'45'dispatch'45'slot'45'stable_464 v0 v1 v2 v4 v5 v6 v7
du_cata'45'dispatch'45'slot'45'stable_464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'dispatch'45'slot'45'stable_464 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             du_cata'45'trace'45'const'45'stable_368 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             du_cata'45'trace'45'nat'45'stable_388 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             du_cata'45'trace'45'linear'45'stable_408 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v7
        -> coe
             du_cata'45'trace'45'branching'45'stable_430 (coe v0) (coe v1)
             (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-stable
d_ir'45'stable_518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_518 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe v2) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_id_22)))
      MAlonzo.Code.Once.IR.C__'8728'__30 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))
             (coe
                d_ir'45'stable_518 (coe v0) (coe v1) (coe v2) (coe v8) (coe v11)
                (coe v5) (coe v6))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (d_ir'45'stable_518
                   (coe v0) (coe v1) (coe v8) (coe v3) (coe v10)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                         (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                            (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v10 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v13 v14
               -> case coe v12 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                 (coe
                                    du_trc_94
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                       (coe v0) (coe v2) (coe v13)
                                       (coe addInt (coe (3 :: Integer)) (coe v5)) (coe v6)
                                       (coe v10)))
                                 (coe
                                    d_ir'45'stable_518 (coe v0) (coe v1) (coe v2) (coe v13)
                                    (coe v10) (coe addInt (coe (3 :: Integer)) (coe v5)) (coe v6))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                          (coe
                                             du_trc_94
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                (coe v0) (coe v2) (coe v14)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                      (coe v0) (coe v2) (coe v13)
                                                      (coe addInt (coe (3 :: Integer)) (coe v5))
                                                      (coe v6) (coe v10)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                         (coe v0) (coe v2) (coe v13)
                                                         (coe addInt (coe (3 :: Integer)) (coe v5))
                                                         (coe v6) (coe v10))))
                                                (coe v11)))
                                          (coe
                                             d_ir'45'stable_518 (coe v0) (coe v1) (coe v2) (coe v14)
                                             (coe v11)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                   (coe v0) (coe v2) (coe v13)
                                                   (coe addInt (coe (3 :: Integer)) (coe v5))
                                                   (coe v6) (coe v10)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                      (coe v0) (coe v2) (coe v13)
                                                      (coe addInt (coe (3 :: Integer)) (coe v5))
                                                      (coe v6) (coe v10)))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                 (coe
                                    du_trc_94
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                       (coe v0) (coe v2) (coe v13)
                                       (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                                       (coe v10)))
                                 (coe
                                    d_ir'45'stable_518 (coe v0) (coe v1) (coe v2) (coe v13)
                                    (coe v10) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                          (coe
                                             du_trc_94
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                (coe v0) (coe v2) (coe v14)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                      (coe v0) (coe v2) (coe v13)
                                                      (coe addInt (coe (4 :: Integer)) (coe v5))
                                                      (coe v6) (coe v10)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                         (coe v0) (coe v2) (coe v13)
                                                         (coe addInt (coe (4 :: Integer)) (coe v5))
                                                         (coe v6) (coe v10))))
                                                (coe v11)))
                                          (coe
                                             d_ir'45'stable_518 (coe v0) (coe v1) (coe v2) (coe v14)
                                             (coe v11)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                   (coe v0) (coe v2) (coe v13)
                                                   (coe addInt (coe (4 :: Integer)) (coe v5))
                                                   (coe v6) (coe v10)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                      (coe v0) (coe v2) (coe v13)
                                                      (coe addInt (coe (4 :: Integer)) (coe v5))
                                                      (coe v6) (coe v10)))))
                                          (coe
                                             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                   (coe addInt (coe (2 :: Integer)) (coe v5)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                      (coe (2 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                         (coe addInt (coe (3 :: Integer)) (coe v5)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v5)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                     (coe
                                                                        addInt (coe (2 :: Integer))
                                                                        (coe v5)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v5)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0)
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v3) (coe v10))
                          (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_fst_44)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_50
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v9) (coe v3))
                          (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_snd_50)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_56 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    seq (coe v9)
                    (coe
                       du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                       (coe
                          du_trc_94
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v11))
                             (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_inl_56 v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_62 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    seq (coe v9)
                    (coe
                       du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                       (coe
                          du_trc_94
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v10) (coe v2))
                             (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_inr_62 v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_70 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                             (coe
                                du_trc_94
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                   (coe v0) (coe v13) (coe v3)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                         (coe v0) (coe v12) (coe v3) (coe v5)
                                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                            (coe v0) (coe v12) (coe v3) (coe v5)
                                            (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10))))
                                   (coe v11)))
                             (coe
                                d_ir'45'stable_518 (coe v0) (coe v1) (coe v13) (coe v3) (coe v11)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                      (coe v0) (coe v12) (coe v3) (coe v5)
                                      (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                         (coe v0) (coe v12) (coe v3) (coe v5)
                                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))))
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                            (coe
                                               du_trc_94
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                  (coe v0) (coe v12) (coe v3) (coe v5)
                                                  (coe addInt (coe (2 :: Integer)) (coe v6))
                                                  (coe v10)))
                                            (coe
                                               d_ir'45'stable_518 (coe v0) (coe v1) (coe v12)
                                               (coe v3) (coe v10) (coe v5)
                                               (coe addInt (coe (2 :: Integer)) (coe v6)))
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v5)
                   (coe v6) (coe MAlonzo.Code.Once.IR.C_terminal_74)))
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v3) (coe v5)
                   (coe v6) (coe MAlonzo.Code.Once.IR.C_initial_78)))
      MAlonzo.Code.Once.IR.C_curry_86 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                (coe
                                                   du_trc_94
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2)
                                                         (coe v12))
                                                      (coe v13) (coe (0 :: Integer))
                                                      (coe addInt (coe (2 :: Integer)) (coe v6))
                                                      (coe v10)))
                                                (coe
                                                   d_ir'45'stable_518 (coe v0) (coe v1)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2)
                                                      (coe v12))
                                                   (coe v13) (coe v10) (coe (0 :: Integer))
                                                   (coe addInt (coe (2 :: Integer)) (coe v6)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                               (coe
                                                                  du_trc_94
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                                                     (coe v0)
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                        (coe v2) (coe v12))
                                                                     (coe v13) (coe (0 :: Integer))
                                                                     (coe
                                                                        addInt (coe (2 :: Integer))
                                                                        (coe v6))
                                                                     (coe v10)))
                                                               (coe
                                                                  d_ir'45'stable_518 (coe v0)
                                                                  (coe v1)
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                     (coe v2) (coe v12))
                                                                  (coe v13) (coe v10)
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     addInt (coe (2 :: Integer))
                                                                     (coe v6)))
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
                      -> coe
                           du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                           (coe
                              du_trc_94
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v11) (coe v3))
                                    (coe v11))
                                 (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_apply_92)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_96 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v3))
                          (coe v3) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_In_96 v8 v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_108 v8 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                      -> coe
                           du_cata'45'dispatch'45'slot'45'stable_464 (coe v0) (coe v1)
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v14)))
                           (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v14)
                                          (coe v3)))
                                    (coe v3) (coe (0 :: Integer)) (coe v6) (coe v11))))
                           (coe
                              du_trc_94
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v14)
                                       (coe v3)))
                                 (coe v3) (coe (0 :: Integer)) (coe v6) (coe v11)))
                           (coe
                              d_ir'45'stable_518 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v14)
                                    (coe v3)))
                              (coe v3) (coe v11) (coe (0 :: Integer)) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v8 v10
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_Para_114 v8 v10)))
      MAlonzo.Code.Once.IR.C_Out_118 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v2))
                          (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_Out_118 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v3))
                          (coe v3) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_122 v8 v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_128 v8 v10
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_Ana_128 v8 v10)))
      MAlonzo.Code.Once.IR.C_Hylo_136 v7 v9 v10 v12 v13
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_Hylo_136 v7 v9 v10 v12 v13)))
      MAlonzo.Code.Once.IR.C_Fuse_144 v7 v9 v10 v12 v13
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_Fuse_144 v7 v9 v10 v12 v13)))
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v7
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v5) (coe v6) (coe v4)))
      MAlonzo.Code.Once.IR.C_const_150 v8 v9
        -> case coe v8 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_const_150 v8 v9)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
                    (coe
                       du_trc_94
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_const_150 v8 v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_156 v7 v8 v9
        -> coe
             du_all'45'stable'63''45'sound_130 (coe v0) (coe v1)
             (coe
                du_trc_94
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_402
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8)) (coe v5)
                   (coe v6) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_666 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_666 v0 v1 v2 v3 v4
  = coe
      d_ir'45'stable_518 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe (0 :: Integer)) (coe (0 :: Integer))
