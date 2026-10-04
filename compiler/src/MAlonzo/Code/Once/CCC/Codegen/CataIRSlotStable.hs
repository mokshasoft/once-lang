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
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.CataIRSlotStable._.CataStrategy
d_CataStrategy_12 a0 = ()
-- Once.CCC.Codegen.CataIRSlotStable._.cata-body
d_cata'45'body_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'body_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'body_90 (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-br-I₁
d_cata'45'br'45'I'8321'_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_362
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-branching
d_cata'45'trace'45'branching_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_44 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'branching_340
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-const
d_cata'45'trace'45'const_46 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'const_46 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'const_352
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-linear
d_cata'45'trace'45'linear_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'linear_48 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'linear_146
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.cata-trace-nat
d_cata'45'trace'45'nat_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'nat_50 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'nat_120
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.ir-to-trace
d_ir'45'to'45'trace_72 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_848
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.ir-to-trace'
d_ir'45'to'45'trace''_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_74 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.ir-to-trace-lab
d_ir'45'to'45'trace'45'lab_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace'45'lab_80 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'lab_924
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.ir-to-unit
d_ir'45'to'45'unit_82 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2326
d_ir'45'to'45'unit_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'unit_842
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.rebuild-walk
d_rebuild'45'walk_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_rebuild'45'walk_92 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.CataIRSlotStable._.resuspend-layer
d_resuspend'45'layer_96 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resuspend'45'layer_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable._.sigop-code
d_sigop'45'code_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_sigop'45'code_100 ~v0 = du_sigop'45'code_100
du_sigop'45'code_100 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_sigop'45'code_100
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_sigop'45'code_500
-- Once.CCC.Codegen.CataIRSlotStable._.visit-walk
d_visit'45'walk_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_visit'45'walk_112 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
      (coe v0)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.AllSlotStable
d_AllSlotStable_132 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_AllSlotStable_132 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.SlotStable
d_SlotStable_134 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> ()
d_SlotStable_134 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.SlotStableT
d_SlotStableT_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_SlotStableT_136 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.trc
d_trc_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trc_142 ~v0 ~v1 v2 = du_trc_142 v2
du_trc_142 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_trc_142 v0
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
d_All'8594'AllI_148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_All'8594'AllI_148 ~v0 ~v1 v2 v3 = du_All'8594'AllI_148 v2 v3
du_All'8594'AllI_148 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_All'8594'AllI_148 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe du_All'8594'AllI_148 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?
d_stable'63'_154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 -> Bool
d_stable'63'_154 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2272 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v4 v5
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe d_all'45'stable'63'_156 (coe v0) (coe v1) (coe v4))
                (coe d_all'45'stable'63'_156 (coe v0) (coe v1) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2314 v4
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> coe v3)
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?
d_all'45'stable'63'_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> Bool
d_all'45'stable'63'_156 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_stable'63'_154 (coe v0) (coe v1) (coe v3))
             (coe d_all'45'stable'63'_156 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.∧-split
d_'8743''45'split_170 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'split_170 ~v0 ~v1 v2 v3 ~v4
  = du_'8743''45'split_170 v2 v3
du_'8743''45'split_170 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'split_170 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?-sound
d_stable'63''45'sound_174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_stable'63''45'sound_174 v0 v1 v2 ~v3
  = du_stable'63''45'sound_174 v0 v1 v2
du_stable'63''45'sound_174 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny
du_stable'63''45'sound_174 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2274 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2278 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2280
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_All'8594'AllI_148 (coe v3)
                (coe du_all'45'stable'63''45'sound_178 (coe v0) (coe v1) (coe v3)))
             (coe
                du_All'8594'AllI_148 (coe v4)
                (coe du_all'45'stable'63''45'sound_178 (coe v0) (coe v1) (coe v4)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2320 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-sound
d_all'45'stable'63''45'sound_178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'stable'63''45'sound_178 v0 v1 v2 ~v3
  = du_all'45'stable'63''45'sound_178 v0 v1 v2
du_all'45'stable'63''45'sound_178 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'stable'63''45'sound_178 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_stable'63''45'sound_174 (coe v0) (coe v1) (coe v3))
             (coe du_all'45'stable'63''45'sound_178 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.AllI→All
d_AllI'8594'All_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_AllI'8594'All_202 ~v0 ~v1 v2 v3 = du_AllI'8594'All_202 v2 v3
du_AllI'8594'All_202 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_AllI'8594'All_202 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                    (coe du_AllI'8594'All_202 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.∧-intro
d_'8743''45'intro_212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'intro_212 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-++
d_all'45'stable'63''45''43''43'_228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45''43''43'_228 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.stable?-complete
d_stable'63''45'complete_242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stable'63''45'complete_242 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.all-stable?-complete
d_all'45'stable'63''45'complete_246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_all'45'stable'63''45'complete_246 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.visit-walk-stable
d_visit'45'walk'45'stable_276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'stable_276 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Once.Type.C_K_112 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_216
                (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
      MAlonzo.Code.Once.Type.C__'8853'__116 v8 v9
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
                         d_visit'45'walk'45'stable_276 (coe v0) (coe v1) (coe v2) (coe v3)
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
                                        d_visit'45'walk'45'stable_276 (coe v0) (coe v1) (coe v2)
                                        (coe v3) (coe v4) (coe v8)
                                        (coe addInt (coe (4 :: Integer)) (coe v6))
                                        (coe addInt (coe (2 :: Integer)) (coe v7)))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
      MAlonzo.Code.Once.Type.C__'8855'__118 v8 v9
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
                            (coe v0) (coe v2) (coe v3) (coe v4) (coe v8)
                            (coe addInt (coe (4 :: Integer)) (coe v6)) (coe v7))
                         (coe
                            d_visit'45'walk'45'stable_276 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe v4) (coe v8) (coe addInt (coe (4 :: Integer)) (coe v6))
                            (coe v7))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  (d_visit'45'walk'45'stable_276
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9)
                                     (coe addInt (coe (4 :: Integer)) (coe v6))
                                     (coe
                                        addInt
                                        (coe
                                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196
                                           (coe v8))
                                        (coe v7))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.rebuild-walk-stable
d_rebuild'45'walk'45'stable_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'stable_338 v0 v1 v2 ~v3 ~v4 v5 v6 v7
  = du_rebuild'45'walk'45'stable_338 v0 v1 v2 v5 v6 v7
du_rebuild'45'walk'45'stable_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'stable_338 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_K_112 v6
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.Type.C__'8853'__116 v6 v7
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
                         du_rebuild'45'walk'45'stable_338 (coe v0) (coe v1) (coe v2)
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
                                                                   du_rebuild'45'walk'45'stable_338
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
      MAlonzo.Code.Once.Type.C__'8855'__118 v6 v7
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
                            (coe v0) (coe v2) (coe v7)
                            (coe addInt (coe (4 :: Integer)) (coe v4))
                            (coe
                               addInt
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v6))
                               (coe v5)))
                         (coe
                            du_rebuild'45'walk'45'stable_338 (coe v0) (coe v1) (coe v2)
                            (coe v7) (coe addInt (coe (4 :: Integer)) (coe v4))
                            (coe
                               addInt
                               (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_196 (coe v6))
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
                                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                        (coe
                                           MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_276
                                           (coe v0) (coe v2) (coe v6)
                                           (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                                        (coe
                                           du_rebuild'45'walk'45'stable_338 (coe v0) (coe v1)
                                           (coe v2) (coe v6)
                                           (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5))
                                        (coe
                                           du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                 (coe addInt (coe (1 :: Integer)) (coe v4)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                    (coe (2 :: Integer)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                       (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                             (coe
                                                                addInt (coe (1 :: Integer))
                                                                (coe v4)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v4)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                         (coe
                                                                            addInt
                                                                            (coe (3 :: Integer))
                                                                            (coe v4)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-body-stable
d_cata'45'body'45'stable_396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'stable_396 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_cata'45'body'45'stable_396 v5 v6
du_cata'45'body'45'stable_396 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'stable_396 v0 v1
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
d_cata'45'trace'45'const'45'stable_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'const'45'stable_416 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'trace'45'const'45'stable_416 v0 v1 v3 v4 v5 v6
du_cata'45'trace'45'const'45'stable_416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'const'45'stable_416 v0 v1 v2 v3 v4 v5
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
         du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
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
      (coe du_cata'45'body'45'stable_396 (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-nat-stable
d_cata'45'trace'45'nat'45'stable_436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'nat'45'stable_436 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'trace'45'nat'45'stable_436 v0 v1 v3 v4 v5 v6
du_cata'45'trace'45'nat'45'stable_436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'nat'45'stable_436 v0 v1 v2 v3 v4 v5
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
         du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
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
      (coe du_cata'45'body'45'stable_396 (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-linear-stable
d_cata'45'trace'45'linear'45'stable_456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'linear'45'stable_456 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'trace'45'linear'45'stable_456 v0 v1 v3 v4 v5 v6
du_cata'45'trace'45'linear'45'stable_456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'linear'45'stable_456 v0 v1 v2 v3 v4 v5
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
         du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
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
      (coe du_cata'45'body'45'stable_396 (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-trace-branching-stable
d_cata'45'trace'45'branching'45'stable_478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'trace'45'branching'45'stable_478 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_cata'45'trace'45'branching'45'stable_478 v0 v1 v2 v4 v5 v6 v7
du_cata'45'trace'45'branching'45'stable_478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'trace'45'branching'45'stable_478 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
         (coe v0) (coe du_cl_498 (coe v2) (coe v3))
         (coe addInt (coe (1 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
         (coe addInt (coe (2 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
         (coe addInt (coe (3 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
         (coe du_bodyL_496 (coe v2) (coe v4)))
      (coe
         du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
            (coe v0) (coe du_cl_498 (coe v2) (coe v3))
            (coe addInt (coe (1 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
            (coe addInt (coe (2 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
            (coe addInt (coe (3 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
            (coe du_bodyL_496 (coe v2) (coe v4))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
            (coe v0) (coe v2) (coe v3) (coe v4))
         (coe
            du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8321'_326
               (coe v0) (coe v2) (coe v3) (coe v4)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
               (coe du_cl_498 (coe v2) (coe v3))
               (coe addInt (coe (1 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
               (coe
                  addInt (coe (3 :: Integer)) (coe du_cl_498 (coe v2) (coe v3))))
            (coe
               du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_112
                  (coe du_cl_498 (coe v2) (coe v3))
                  (coe addInt (coe (1 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))
                  (coe
                     addInt (coe (3 :: Integer)) (coe du_cl_498 (coe v2) (coe v3)))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                  (coe v0) (coe v3) (coe v4))
               (coe
                  du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'br'45'I'8322'_334
                     (coe v0) (coe v3) (coe v4)))
               (coe du_cata'45'body'45'stable_396 (coe v5) (coe v6)))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.bodyL
d_bodyL_496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_bodyL_496 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 = du_bodyL_496 v2 v5
du_bodyL_496 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_bodyL_496 v0 v1
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
d_cl_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_cl_498 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 = du_cl_498 v2 v4
du_cl_498 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_cl_498 v0 v1
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
d_I'8321''45'true_500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_I'8321''45'true_500 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.cata-dispatch-slot-stable
d_cata'45'dispatch'45'slot'45'stable_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'slot'45'stable_512 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_cata'45'dispatch'45'slot'45'stable_512 v0 v1 v2 v4 v5 v6 v7
du_cata'45'dispatch'45'slot'45'stable_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'dispatch'45'slot'45'stable_512 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             du_cata'45'trace'45'const'45'stable_416 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             du_cata'45'trace'45'nat'45'stable_436 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             du_cata'45'trace'45'linear'45'stable_456 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v7
        -> coe
             du_cata'45'trace'45'branching'45'stable_478 (coe v0) (coe v1)
             (coe v7) (coe v3) (coe v4) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.sigop-stable
d_sigop'45'stable_568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sigop'45'stable_568 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_sigop'45'stable_568 v0 v1 v2 v3 v4 v5 v6
du_sigop'45'stable_568 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sigop'45'stable_568 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v5)
      (coe
         du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_sigop'45'code_500
            (coe v2) (coe v3) (coe v4) (coe v6) (coe v5)))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-stable
d_ir'45'stable_594 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'stable_594 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe v2) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_id_20)))
      MAlonzo.Code.Once.IR.C__'8728'__28 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))
             (coe
                d_ir'45'stable_594 (coe v0) (coe v1) (coe v2) (coe v8) (coe v11)
                (coe v5) (coe v6))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (d_ir'45'stable_594
                   (coe v0) (coe v1) (coe v8) (coe v3) (coe v10)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                         (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                            (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                          (coe
                             du_trc_142
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                (coe v0) (coe v2) (coe v12)
                                (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6) (coe v10)))
                          (coe
                             d_ir'45'stable_594 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10)
                             (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                   (coe
                                      du_trc_142
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                         (coe v0) (coe v2) (coe v13)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                               (coe v0) (coe v2) (coe v12)
                                               (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                                               (coe v10)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                                  (coe v0) (coe v2) (coe v12)
                                                  (coe addInt (coe (4 :: Integer)) (coe v5))
                                                  (coe v6) (coe v10))))
                                         (coe v11)))
                                   (coe
                                      d_ir'45'stable_594 (coe v0) (coe v1) (coe v2) (coe v13)
                                      (coe v11)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                            (coe v0) (coe v2) (coe v12)
                                            (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                                            (coe v10)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                               (coe v0) (coe v2) (coe v12)
                                               (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                                               (coe v10)))))
                                   (coe
                                      du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                            (coe addInt (coe (2 :: Integer)) (coe v5)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                               (coe (2 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                  (coe addInt (coe (3 :: Integer)) (coe v5)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                        (coe addInt (coe (1 :: Integer)) (coe v5)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                              (coe
                                                                 addInt (coe (2 :: Integer))
                                                                 (coe v5)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                    (coe
                                                                       addInt (coe (3 :: Integer))
                                                                       (coe v5)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0)
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v3) (coe v10))
                          (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_fst_42)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_snd_48
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v9) (coe v3))
                          (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_snd_48)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe v2)
                          (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v10))
                          (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_inl_54)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_60
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe v2)
                          (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v9) (coe v2)) (coe v5)
                          (coe v6) (coe MAlonzo.Code.Once.IR.C_inr_60)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_68 v10 v11
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
                                du_trc_142
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                   (coe v0) (coe v13) (coe v3)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                         (coe v0) (coe v12) (coe v3) (coe v5)
                                         (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                            (coe v0) (coe v12) (coe v3) (coe v5)
                                            (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10))))
                                   (coe v11)))
                             (coe
                                d_ir'45'stable_594 (coe v0) (coe v1) (coe v13) (coe v3) (coe v11)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                      (coe v0) (coe v12) (coe v3) (coe v5)
                                      (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
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
                                               du_trc_142
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                                  (coe v0) (coe v12) (coe v3) (coe v5)
                                                  (coe addInt (coe (2 :: Integer)) (coe v6))
                                                  (coe v10)))
                                            (coe
                                               d_ir'45'stable_594 (coe v0) (coe v1) (coe v12)
                                               (coe v3) (coe v10) (coe v5)
                                               (coe addInt (coe (2 :: Integer)) (coe v6)))
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v5)
                   (coe v6) (coe MAlonzo.Code.Once.IR.C_terminal_72)))
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18) (coe v3) (coe v5)
                   (coe v6) (coe MAlonzo.Code.Once.IR.C_initial_76)))
      MAlonzo.Code.Once.IR.C_curry_84 v10
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_curry_84 v10)))
      MAlonzo.Code.Once.IR.C_apply_90
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
                      -> coe
                           du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                           (coe
                              du_trc_142
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v11) (coe v3))
                                    (coe v11))
                                 (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_apply_90)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_94 v8
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v9) (coe v3))
                          (coe v3) (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_In_94 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v9) (coe v2))
                          (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v8 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                      -> coe
                           du_cata'45'dispatch'45'slot'45'stable_512 (coe v0) (coe v1)
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608 (coe v14)))
                           (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v14)
                                          (coe v3)))
                                    (coe v3) (coe (0 :: Integer)) (coe v6) (coe v11))))
                           (coe
                              du_trc_142
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v14)
                                       (coe v3)))
                                 (coe v3) (coe (0 :: Integer)) (coe v6) (coe v11)))
                           (coe
                              d_ir'45'stable_594 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v14)
                                    (coe v3)))
                              (coe v3) (coe v11) (coe (0 :: Integer)) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v9) (coe v2))
                          (coe v5) (coe v6) (coe MAlonzo.Code.Once.IR.C_Out_110 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v8
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v9) (coe v3))
                          (coe v3) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_in'45'ν_114 v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_120 v8 v10
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_Ana_120 v8 v10)))
      MAlonzo.Code.Once.IR.C_const_124 v8 v9
        -> case coe v8 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_520
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Int_30) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_const_124 v8 v9)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_522
               -> coe
                    du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                    (coe
                       du_trc_142
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.C_Float_32) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Once.IR.C_const_124 v8 v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_130 v7 v8 v9
        -> coe
             du_sigop'45'stable_568 (coe v0) (coe v1) (coe v7) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v9)))
             (coe v5)
      MAlonzo.Code.Once.IR.C_Call_136 v9
        -> coe
             du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
             (coe
                du_trc_142
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe v3) (coe v5) (coe v6)
                   (coe MAlonzo.Code.Once.IR.C_Call_136 v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.bds
d_bds_706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bds_706 ~v0 ~v1 v2 = du_bds_706 v2
du_bds_706 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bds_706 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v6
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.BlockStable
d_BlockStable_710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_BlockStable_710 = erased
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.blocks-stable
d_blocks'45'stable_716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'stable_716 ~v0 ~v1 v2 v3
  = du_blocks'45'stable_716 v2 v3
du_blocks'45'stable_716 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'stable_716 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v1 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v10 v11
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
                                           (coe
                                              MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v4))
                                           (coe v6)))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238
                                                 (coe v6)))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                        (coe v7) (coe v10)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                                  (coe du_blocks'45'stable_716 (coe v3) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.resuspend-stable
d_resuspend'45'stable_740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resuspend'45'stable_740 v0 ~v1 v2 v3 v4 v5 v6
  = du_resuspend'45'stable_740 v0 v2 v3 v4 v5 v6
du_resuspend'45'stable_740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_resuspend'45'stable_740 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
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
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v10 v11
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
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                   (coe v1))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                               (coe v0)
                                               (coe
                                                  du_n2_786 (coe v0) (coe v1) (coe v2) (coe v3)
                                                  (coe v10) (coe v8))
                                               (coe
                                                  du_l2_788 (coe v0) (coe v1) (coe v2) (coe v3)
                                                  (coe v10) (coe v8))
                                               (coe v3) (coe v11) (coe v9))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                            (coe addInt (coe (2 :: Integer)) (coe v1)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                               (coe (2 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                  (coe addInt (coe (1 :: Integer)) (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                        (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                              (coe (1 :: Integer)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                    (coe
                                                                       addInt (coe (1 :: Integer))
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                             (coe
                                du_arm_794
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                         (coe v0)
                                         (coe
                                            du_n2_786 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                            (coe v8))
                                         (coe
                                            du_l2_788 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                            (coe v8))
                                         (coe v3) (coe v11) (coe v9))))
                                (coe
                                   du_resuspend'45'stable_740 (coe v0)
                                   (coe
                                      du_n2_786 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v8))
                                   (coe
                                      du_l2_788 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                      (coe v8))
                                   (coe v3) (coe v11) (coe v9)))
                             (coe
                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                (coe
                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                   (coe
                                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                                        (coe v0)
                                                        (coe addInt (coe (3 :: Integer)) (coe v1))
                                                        (coe addInt (coe (2 :: Integer)) (coe v2))
                                                        (coe v3) (coe v10) (coe v8))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                     (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                        (coe (2 :: Integer)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                 (coe
                                                                    addInt (coe (2 :: Integer))
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                       (coe (0 :: Integer)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                             (coe
                                                                                addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe v1)))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                                      (coe
                                         du_arm_794
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                                  (coe v0)
                                                  (coe addInt (coe (3 :: Integer)) (coe v1))
                                                  (coe addInt (coe (2 :: Integer)) (coe v2))
                                                  (coe v3) (coe v10) (coe v8))))
                                         (coe
                                            du_resuspend'45'stable_740 (coe v0)
                                            (coe addInt (coe (3 :: Integer)) (coe v1))
                                            (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                            (coe v10) (coe v8)))
                                      (coe
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v10 v11
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
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                      (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                      (coe v3) (coe v10) (coe v8))))
                             (coe
                                du_resuspend'45'stable_740 (coe v0)
                                (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                (coe v10) (coe v8))
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
                                                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
                                                                 (coe v0)
                                                                 (coe
                                                                    du_n2_768 (coe v0) (coe v1)
                                                                    (coe v2) (coe v3) (coe v10)
                                                                    (coe v8))
                                                                 (coe
                                                                    du_l2_770 (coe v0) (coe v1)
                                                                    (coe v2) (coe v3) (coe v10)
                                                                    (coe v8))
                                                                 (coe v3) (coe v11) (coe v9))))
                                                        (coe
                                                           du_resuspend'45'stable_740 (coe v0)
                                                           (coe
                                                              du_n2_768 (coe v0) (coe v1) (coe v2)
                                                              (coe v3) (coe v10) (coe v8))
                                                           (coe
                                                              du_l2_770 (coe v0) (coe v1) (coe v2)
                                                              (coe v3) (coe v10) (coe v8))
                                                           (coe v3) (coe v11) (coe v9))
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
                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.n2
d_n2_768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_n2_768 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_n2_768 v0 v2 v3 v4 v5 v7
du_n2_768 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_n2_768 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
         (coe v3) (coe v4) (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.l2
d_l2_770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_l2_770 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_l2_770 v0 v2 v3 v4 v5 v7
du_l2_770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_l2_770 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
            (coe v3) (coe v4) (coe v5)))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.n2
d_n2_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_n2_786 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_n2_786 v0 v2 v3 v4 v5 v7
du_n2_786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_n2_786 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
         (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
         (coe v5))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.l2
d_l2_788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_l2_788 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_l2_788 v0 v2 v3 v4 v5 v7
du_l2_788 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
du_l2_788 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_resuspend'45'layer_400
            (coe v0) (coe addInt (coe (3 :: Integer)) (coe v1))
            (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
            (coe v5)))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable._.arm
d_arm_794 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_arm_794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_arm_794 v10 v11
du_arm_794 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_arm_794 v0 v1
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
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-blocks-stable
d_ir'45'blocks'45'stable_810 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'blocks'45'stable_810 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C__'8728'__28 v8 v10 v11
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                du_bds_706
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                   (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))
             (coe
                d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v2) (coe v8)
                (coe v11) (coe v5) (coe v6))
             (coe
                d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v8) (coe v3)
                (coe v10)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                      (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                         (coe v0) (coe v2) (coe v8) (coe v5) (coe v6) (coe v11)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bds_706
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe v2) (coe v12)
                          (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6) (coe v10)))
                    (coe
                       d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v2) (coe v12)
                       (coe v10) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                    (coe
                       d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v2) (coe v13)
                       (coe v11)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                             (coe v0) (coe v2) (coe v12)
                             (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6) (coe v10)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                (coe v0) (coe v2) (coe v12)
                                (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6) (coe v10)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_case_68 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_bds_706
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                          (coe v0) (coe v12) (coe v3) (coe v5)
                          (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                    (coe
                       d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v12) (coe v3)
                       (coe v10) (coe v5) (coe addInt (coe (2 :: Integer)) (coe v6)))
                    (coe
                       d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v13) (coe v3)
                       (coe v11)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                             (coe v0) (coe v12) (coe v3) (coe v5)
                             (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                (coe v0) (coe v12) (coe v3) (coe v5)
                                (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_curry_84 v10
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (d_ir'45'stable_594
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v11))
                       (coe v12) (coe v10) (coe (0 :: Integer))
                       (coe addInt (coe (2 :: Integer)) (coe v6)))
                    (d_ir'45'blocks'45'stable_810
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v11))
                       (coe v12) (coe v10) (coe (0 :: Integer))
                       (coe addInt (coe (2 :: Integer)) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_In_94 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Cata_106 v8 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                      -> coe
                           d_ir'45'blocks'45'stable_810 (coe v0) (coe v1)
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v14) (coe v3)))
                           (coe v3) (coe v11) (coe (0 :: Integer)) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v8
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                du_all'45'stable'63''45'sound_178 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Ana_120 v8 v10
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                       (coe
                          du_trc_142
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                             (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v11) (coe v2))
                             (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v6))
                             (coe v10)))
                       (coe
                          d_ir'45'stable_594 (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v11) (coe v2))
                          (coe v10) (coe (0 :: Integer))
                          (coe addInt (coe (1 :: Integer)) (coe v6)))
                       (coe
                          du_resuspend'45'stable_740 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                (coe v0) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v11) (coe v2))
                                (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v6))
                                (coe v10)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                                   (coe v0) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v11)
                                      (coe v2))
                                   (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v6))
                                   (coe v10))))
                          (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))
                          (coe v11) (coe v8)))
                    (d_ir'45'blocks'45'stable_810
                       (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v11) (coe v2))
                       (coe v10) (coe (0 :: Integer))
                       (coe addInt (coe (1 :: Integer)) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v8 v9
        -> coe
             seq (coe v8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_SigOp_130 v7 v8 v9
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Call_136 v9
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-to-trace-slot-stable
d_ir'45'to'45'trace'45'slot'45'stable_928 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'slot'45'stable_928 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         du_trc_142
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
            (coe v0) (coe v2) (coe v3) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v4)))
      (coe
         d_ir'45'stable_594 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            du_blocks'45'stable_716
            (coe
               du_bds_706
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                  (coe v0) (coe v2) (coe v3) (coe (0 :: Integer))
                  (coe (0 :: Integer)) (coe v4)))
            (coe
               d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe (0 :: Integer)) (coe (0 :: Integer)))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-to-trace-lab-slot-stable
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_940 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'lab'45'slot'45'stable_940 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         du_trc_142
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
            (coe v0) (coe v2) (coe v3) (coe (0 :: Integer)) (coe v5) (coe v4)))
      (coe
         d_ir'45'stable_594 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe (0 :: Integer)) (coe v5))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            du_blocks'45'stable_716
            (coe
               du_bds_706
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                  (coe v0) (coe v2) (coe v3) (coe (0 :: Integer)) (coe v5) (coe v4)))
            (coe
               d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe (0 :: Integer)) (coe v5))))
-- Once.CCC.Codegen.CataIRSlotStable.CataIRSlotStable.ir-to-trace-top-slot-stable
d_ir'45'to'45'trace'45'top'45'slot'45'stable_954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'top'45'slot'45'stable_954 v0 v1 v2 v3 v4 ~v5
  = du_ir'45'to'45'trace'45'top'45'slot'45'stable_954 v0 v1 v2 v3 v4
du_ir'45'to'45'trace'45'top'45'slot'45'stable_954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ir'45'to'45'trace'45'top'45'slot'45'stable_954 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         du_trc_142
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
            (coe v0) (coe v2) (coe v3) (coe (0 :: Integer))
            (coe (0 :: Integer)) (coe v4)))
      (coe
         d_ir'45'stable_594 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe (0 :: Integer)) (coe (0 :: Integer)))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               du_blocks'45'stable_716
               (coe
                  du_bds_706
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_530
                     (coe v0) (coe v2) (coe v3) (coe (0 :: Integer))
                     (coe (0 :: Integer)) (coe v4)))
               (coe
                  d_ir'45'blocks'45'stable_810 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe v4) (coe (0 :: Integer)) (coe (0 :: Integer))))))
