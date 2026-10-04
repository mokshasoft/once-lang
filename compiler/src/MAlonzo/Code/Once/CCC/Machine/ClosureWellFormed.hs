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

module MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ClosureWellFormed._.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace'45'at'45'frontier_14 v0 ~v1
  = du_ir'45'to'45'trace'45'at'45'frontier_14 v0
du_ir'45'to'45'trace'45'at'45'frontier_14 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_ir'45'to'45'trace'45'at'45'frontier_14 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'at'45'frontier_856
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.evalᴰ
d_eval'7472'_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_eval'7472'_24 ~v0 v1 v2 v3 v4 = du_eval'7472'_24 v1 v2 v3 v4
du_eval'7472'_24 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_eval'7472'_24 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166 (coe v1))
      (coe
         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166 (coe v1))
         (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_162 (coe v1))
         (coe v0))
      (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ιᶠ
d_ι'7584'_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
d_ι'7584'_26 ~v0 ~v1 v2 = du_ι'7584'_26 v2
du_ι'7584'_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458
du_ι'7584'_26 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump
d_AllocBump_34 a0 a1 a2 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.BeforeFrontier
d_BeforeFrontier_38 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.apply-bump
d_apply'45'bump_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_apply'45'bump_42 ~v0 ~v1 ~v2 = du_apply'45'bump_42
du_apply'45'bump_42 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_apply'45'bump_42
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_942
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_84 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 -> Integer
d_next'45'heap'45'ref'45'delta_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_938
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_86 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 -> Integer
d_next'45'slot'45'delta_86 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_936
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.readLoc
d_readLoc_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_112 ~v0 ~v1 ~v2 = du_readLoc_112
du_readLoc_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_112
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.writeLoc
d_writeLoc_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_writeLoc_120 ~v0 ~v1 v2 = du_writeLoc_120 v2
du_writeLoc_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
du_writeLoc_120 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_832 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.write-loc
d_write'45'loc_150 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_write'45'loc_150 ~v0 ~v1 v2 = du_write'45'loc_150 v2
du_write'45'loc_150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
du_write'45'loc_150 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_write'45'loc_336
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.exec-trace
d_exec'45'trace_224 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_224 ~v0 ~v1 v2 = du_exec'45'trace_224 v2
du_exec'45'trace_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_224 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3242 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.TraceWF
d_TraceWF_300 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.SumTag
d_SumTag_546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_546 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_570 ::
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
d_transport'45'SumTag_570 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.prim-sv
d_prim'45'sv_582 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_582 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_prim'45'sv_582 v4 v5
du_prim'45'sv_582 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_582 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_520
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Int_134)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_202) (coe v1)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_522
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Float_136)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_204) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlineRep
d_InlineRep_590 a0 a1 a2 a3 = ()
data T_InlineRep_590
  = C_rep'45'prim_594 MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 |
    C_rep'45'unit_596 MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.inline-sv
d_inline'45'sv_600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_600 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_inline'45'sv_600 v4 v5
du_inline'45'sv_600 ::
  T_InlineRep_590 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_600 v0 v1
  = case coe v0 of
      C_rep'45'prim_594 v2 -> coe du_prim'45'sv_582 (coe v2) (coe v1)
      C_rep'45'unit_596 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.CellAt
d_CellAt_612 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_CellAt_612
  = C_cell'45'ptr_816 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.IR.T_AllocMode_4
                      MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                      T_ValidAtWF_616 |
    C_cell'45'inline_828 T_InlineRep_590
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_616 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ValidAtWF_616
  = C_valid'45'unit'45'wf_838 |
    C_valid'45'pair'45'wf_856 AgdaAny
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                              T_CellAt_612 T_CellAt_612 |
    C_valid'45'closure'45'wf_882 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                 MAlonzo.Code.Once.IR.T_AllocMode_4
                                 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                                 T_ValidAtWF_616 |
    C_valid'45'closure'45'reg'45'wf_906 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                        MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                        MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                                        T_InlineRep_590
                                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_valid'45'ν'45'susp'45'wf_926 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                   MAlonzo.Code.Once.IRTy.T_WellFormedFI_122
                                   MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                   MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny T_CellAt_612
                                   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_valid'45'inl'45'wf_946 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                             T_ValidAtWF_616 |
    C_valid'45'inr'45'wf_966 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                             T_ValidAtWF_616 |
    C_valid'45'inl'45'reg'45'wf_984 AgdaAny T_InlineRep_590
                                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_valid'45'inr'45'reg'45'wf_1002 AgdaAny T_InlineRep_590
                                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_valid'45'μ'45'wf_1018 MAlonzo.Code.Once.IRTy.T_WellFormedFI_122
                            T_ValidAtWF_616 |
    C_valid'45'int'45'wf_1030 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_valid'45'float'45'wf_1042 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_632 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ValidAtWF_616
d_valid'45'primitive'45'wf_632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9 v10 ~v11
  = du_valid'45'primitive'45'wf_632 v9 v10
du_valid'45'primitive'45'wf_632 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616
du_valid'45'primitive'45'wf_632 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_520
        -> coe C_valid'45'int'45'wf_1030 v1
      MAlonzo.Code.Once.IRTy.C_fits'45'float_522
        -> coe C_valid'45'float'45'wf_1042 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ResultPlace
d_ResultPlace_646 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ResultPlace_646
  = C_unit'45'result_1060 |
    C_at'45'loc_1076 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                     T_ValidAtWF_616
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                     T_ValidAtWF_616
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_at'45'reg_1092 MAlonzo.Code.Once.IRTy.T_FitsInRegI_518
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-sv
d_place'45'sv_660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_ResultPlace_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_unit'45'result_1060
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70
                (coe d_unit'45'result'45'sv'45'loc_1104 v0 v1 v2 v4 v5 v6 v8))
      C_at'45'loc_1076 v16 v17 v18 v20 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v16)
      C_at'45'reg_1092 v16 -> coe du_prim'45'sv_582 (coe v16) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-rax
d_place'45'rax_676 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_ResultPlace_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_676 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase
d_IRResultBase_692 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultBase_692
  = C_constructor_1204 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 Integer
                       AgdaAny T_ResultPlace_646
                       MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 AgdaAny
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_702 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IRStackBudget_702
  = C_constructor_1276 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                       AgdaAny AgdaAny AgdaAny AgdaAny Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_710 a0 a1 a2 a3 a4 a5 = ()
data T_IRHeapBudget_710
  = C_constructor_1306 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_726 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultAWF_726
  = C_constructor_1412 T_IRResultBase_692 T_IRStackBudget_702
                       T_IRHeapBudget_710
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_784 ::
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
  T_ResultPlace_646 ->
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
  T_IRStackBudget_702 -> T_IRHeapBudget_710 -> T_IRResultAWF_726
d_mk'45'IRResultAWF'45'via'45'bump_784 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14 ~v15 ~v16 ~v17 v18 v19 v20
                                       ~v21 ~v22 v23 ~v24 v25 v26 v27
  = du_mk'45'IRResultAWF'45'via'45'bump_784
      v10 v12 v13 v18 v19 v20 v23 v25 v26 v27
du_mk'45'IRResultAWF'45'via'45'bump_784 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  Integer ->
  AgdaAny ->
  T_ResultPlace_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  AgdaAny ->
  T_IRStackBudget_702 -> T_IRHeapBudget_710 -> T_IRResultAWF_726
du_mk'45'IRResultAWF'45'via'45'bump_784 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = coe
      C_constructor_1412 (coe C_constructor_1204 v0 v1 v2 v3 v4 v5 v6 v7)
      (coe v8) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_800 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_BodyCorrect_800
  = C_constructor_1516 Integer
                       (AgdaAny ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        T_ValidAtWF_616 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc
d_unit'45'result'45'sv'45'loc_1104
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub
d_rax'45'stub_1116
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_1166 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_final'45'state_1166 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace
d_trace_1168 ::
  T_IRResultBase_692 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trace_1168 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.bump
d_bump_1170 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_1170 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1172 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1172 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_1174 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1174 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_1176 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1176 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.obs-budget
d_obs'45'budget_1178 :: T_IRResultBase_692 -> Integer
d_obs'45'budget_1178 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.ir-returns
d_ir'45'returns_1180 :: T_IRResultBase_692 -> AgdaAny
d_ir'45'returns_1180 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_1182 :: T_IRResultBase_692 -> T_ResultPlace_646
d_result'45'place_1182 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_1184 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1184 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_1188 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1188 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_1190 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_1190 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_1196 ::
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1196 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1198 :: T_IRResultBase_692 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1198 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v7 v8 v9 v12 v14 -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_1200 ::
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
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_1200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1200 v9 v10
du_final'45'alloc_1200 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_IRResultBase_692 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_1200 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_942
      (coe d_bump_1170 (coe v1)) (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_1202 ::
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
  T_IRResultBase_692 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1202 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_1242 :: T_IRStackBudget_702 -> Integer
d_max'45'slot'45'written_1242 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_1244 :: T_IRStackBudget_702 -> Integer
d_stack'45'budget_1244 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1246 ::
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1246 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1248 ::
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1248 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1250 ::
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1250 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_1256 ::
  T_IRStackBudget_702 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1256 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_1258 :: T_IRStackBudget_702 -> AgdaAny
d_trace'45'writes'45'above_1258 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1260 ::
  T_IRStackBudget_702 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1260 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_1262 :: T_IRStackBudget_702 -> AgdaAny
d_trace'45'writes'45'below_1262 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1264 ::
  T_IRStackBudget_702 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1264 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_1266 :: T_IRStackBudget_702 -> Integer
d_scratch'45'budget_1266 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_1268 ::
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1268 v0
  = case coe v0 of
      C_constructor_1276 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_1270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1270 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_slot'45'monotone_1270 v3
du_slot'45'monotone_1270 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1270 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1272 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7
  = du_slot'45'stays'45'in'45'budget_1272 v3 v4 v7
du_slot'45'stays'45'in'45'budget_1272 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  T_IRStackBudget_702 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1272 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_936
         (coe v1))
      (d_stack'45'budget_1244 (coe v2))
      (d_bump'45'fits'45'stack'45'budget_1246 (coe v2))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_1294 :: T_IRHeapBudget_710 -> Integer
d_heap'45'budget_1294 v0
  = case coe v0 of
      C_constructor_1306 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1296 ::
  T_IRHeapBudget_710 -> Integer
d_max'45'heap'45'ref'45'written_1296 v0
  = case coe v0 of
      C_constructor_1306 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1298 ::
  T_IRHeapBudget_710 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1298 v0
  = case coe v0 of
      C_constructor_1306 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1300 ::
  T_IRHeapBudget_710 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1300 v0
  = case coe v0 of
      C_constructor_1306 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1302 ::
  T_IRHeapBudget_710 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1302 v0
  = case coe v0 of
      C_constructor_1306 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_1304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  T_IRHeapBudget_710 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1304 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_heap'45'monotone_1304 v3
du_heap'45'monotone_1304 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1304 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.base
d_base_1328 :: T_IRResultAWF_726 -> T_IRResultBase_692
d_base_1328 v0
  = case coe v0 of
      C_constructor_1412 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_1330 :: T_IRResultAWF_726 -> T_IRStackBudget_702
d_stack'45'inv_1330 v0
  = case coe v0 of
      C_constructor_1412 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_1332 :: T_IRResultAWF_726 -> T_IRHeapBudget_710
d_heap'45'inv_1332 v0
  = case coe v0 of
      C_constructor_1412 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.alloc-correct
d_alloc'45'correct_1336 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1336 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump
d_bump_1338 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_930
d_bump_1338 v0 = coe d_bump_1170 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-alloc
d_final'45'alloc_1340 ::
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
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_final'45'alloc_1340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1340 v9 v10
du_final'45'alloc_1340 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_final'45'alloc_1340 v0 v1
  = coe du_final'45'alloc_1200 (coe v0) (coe d_base_1328 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-state
d_final'45'state_1342 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_final'45'state_1342 v0
  = coe d_final'45'state_1166 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frame-preserved
d_frame'45'preserved_1344 ::
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
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1344 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.ir-returns
d_ir'45'returns_1346 :: T_IRResultAWF_726 -> AgdaAny
d_ir'45'returns_1346 v0
  = coe d_ir'45'returns_1180 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.mem-preserved-before
d_mem'45'preserved'45'before_1348 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1348 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.not-halted
d_not'45'halted_1350 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1350 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.obs-budget
d_obs'45'budget_1352 :: T_IRResultAWF_726 -> Integer
d_obs'45'budget_1352 v0
  = coe d_obs'45'budget_1178 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.result-place
d_result'45'place_1354 :: T_IRResultAWF_726 -> T_ResultPlace_646
d_result'45'place_1354 v0
  = coe d_result'45'place_1182 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace
d_trace_1356 ::
  T_IRResultAWF_726 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_trace_1356 v0 = coe d_trace_1168 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-correct
d_trace'45'correct_1358 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1358 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1360 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1360 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1362 :: T_IRResultAWF_726 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1362 v0
  = coe d_trace'45'no'45'frame'45'ops_1198 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-preserves-halted
d_trace'45'preserves'45'halted_1364 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1364 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-twf
d_trace'45'twf_1366 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8440
d_trace'45'twf_1366 v0
  = coe d_trace'45'twf_1190 (coe d_base_1328 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1370 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1370 v0
  = coe
      d_bump'45'fits'45'stack'45'budget_1246
      (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frontier-slot-stable
d_frontier'45'slot'45'stable_1372 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1372 v0
  = coe
      d_frontier'45'slot'45'stable_1256
      (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1374 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1374 v0
  = coe
      d_max'45'slot'45'geq'45'final_1248
      (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1376 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1376 v0
  = coe
      d_max'45'slot'45'usage'45'bound_1250
      (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-written
d_max'45'slot'45'written_1378 :: T_IRResultAWF_726 -> Integer
d_max'45'slot'45'written_1378 v0
  = coe
      d_max'45'slot'45'written_1242 (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-bounded
d_scratch'45'bounded_1380 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1380 v0
  = coe d_scratch'45'bounded_1268 (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-budget
d_scratch'45'budget_1382 :: T_IRResultAWF_726 -> Integer
d_scratch'45'budget_1382 v0
  = coe d_scratch'45'budget_1266 (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-monotone
d_slot'45'monotone_1384 ::
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
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_1384 v9
du_slot'45'monotone_1384 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1384 v0 = coe du_slot'45'monotone_1270 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1386 ::
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
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_1386 v9 v10
du_slot'45'stays'45'in'45'budget_1386 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1386 v0 v1
  = coe
      du_slot'45'stays'45'in'45'budget_1272 (coe v0)
      (coe d_bump_1170 (coe d_base_1328 (coe v1)))
      (coe d_stack'45'inv_1330 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.stack-budget
d_stack'45'budget_1388 :: T_IRResultAWF_726 -> Integer
d_stack'45'budget_1388 v0
  = coe d_stack'45'budget_1244 (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1390 ::
  T_IRResultAWF_726 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1390 v0
  = coe
      d_trace'45'slot'45'reads'45'above_1260
      (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1392 ::
  T_IRResultAWF_726 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1392 v0
  = coe
      d_trace'45'slot'45'reads'45'below_1264
      (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-above
d_trace'45'writes'45'above_1394 :: T_IRResultAWF_726 -> AgdaAny
d_trace'45'writes'45'above_1394 v0
  = coe
      d_trace'45'writes'45'above_1258 (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-below
d_trace'45'writes'45'below_1396 :: T_IRResultAWF_726 -> AgdaAny
d_trace'45'writes'45'below_1396 v0
  = coe
      d_trace'45'writes'45'below_1262 (coe d_stack'45'inv_1330 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1400 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1400 v0
  = coe
      d_bump'45'fits'45'heap'45'budget_1298
      (coe d_heap'45'inv_1332 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-budget
d_heap'45'budget_1402 :: T_IRResultAWF_726 -> Integer
d_heap'45'budget_1402 v0
  = coe d_heap'45'budget_1294 (coe d_heap'45'inv_1332 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-monotone
d_heap'45'monotone_1404 ::
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
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_1404 v9
du_heap'45'monotone_1404 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1404 v0 = coe du_heap'45'monotone_1304 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1406 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1406 v0
  = coe
      d_max'45'heap'45'ref'45'geq'45'final_1300
      (coe d_heap'45'inv_1332 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1408 ::
  T_IRResultAWF_726 -> Integer
d_max'45'heap'45'ref'45'written_1408 v0
  = coe
      d_max'45'heap'45'ref'45'written_1296
      (coe d_heap'45'inv_1332 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1410 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1410 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1302
      (coe d_heap'45'inv_1332 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_1496 :: T_BodyCorrect_800 -> Integer
d_body'45'capacity_1496 v0
  = case coe v0 of
      C_constructor_1516 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_1498 ::
  T_BodyCorrect_800 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_1498 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.execute
d_execute_1514 ::
  T_BodyCorrect_800 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_1514 v0
  = case coe v0 of
      C_constructor_1516 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_1534 ::
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
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_1534 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-via-budget
d_bound'45'via'45'budget_1546 ::
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
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'via'45'budget_1546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 v10 ~v11
  = du_bound'45'via'45'budget_1546 v10
du_bound'45'via'45'budget_1546 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'via'45'budget_1546 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1302
      (coe d_heap'45'inv_1332 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-alloc
d_bound'45'alloc_1550 ::
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
  T_IRResultAWF_726 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'alloc_1550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      ~v11
  = du_bound'45'alloc_1550 v10
du_bound'45'alloc_1550 ::
  T_IRResultAWF_726 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'alloc_1550 v0
  = coe du_bound'45'via'45'budget_1546 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_1578 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14
  = ()
data T_ClosureWellFormed_1578
  = C_constructor_1636 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                       MAlonzo.Code.Once.IR.T_AllocMode_4 T_ValidAtWF_616
                       T_BodyCorrect_800
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_1620 ::
  T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1620 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_1622 ::
  T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1622 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_1624 ::
  T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_env'45'before_1624 v0
  = case coe v0 of
      C_constructor_1636 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_1626 ::
  T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_code'45'before_1626 v0
  = case coe v0 of
      C_constructor_1636 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_1628 ::
  T_ClosureWellFormed_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_1628 v0
  = case coe v0 of
      C_constructor_1636 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_1630 ::
  T_ClosureWellFormed_1578 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1630 v0
  = case coe v0 of
      C_constructor_1636 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_1632 :: T_ClosureWellFormed_1578 -> T_ValidAtWF_616
d_env'45'valid_1632 v0
  = case coe v0 of
      C_constructor_1636 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_1634 ::
  T_ClosureWellFormed_1578 -> T_BodyCorrect_800
d_body'45'correct_1634 v0
  = case coe v0 of
      C_constructor_1636 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.EnvAt
d_EnvAt_1648 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_EnvAt_1648
  = C_env'45'at'45'loc_1664 MAlonzo.Code.Once.IR.T_AllocMode_4
                            MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                            MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                            T_ValidAtWF_616 |
    C_env'45'in'45'cell_1668 T_InlineRep_590
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_1682 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ClosureValidWF_1682
  = C_constructor_1736 MAlonzo.Code.Once.IRTy.T_IRTy_6
                       MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                       MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny T_EnvAt_1648
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_1716 ::
  T_ClosureValidWF_1682 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1716 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body
d_body_1718 ::
  T_ClosureValidWF_1682 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1718 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env
d_env_1720 :: T_ClosureValidWF_1682 -> AgdaAny
d_env_1720 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_1722 ::
  T_ClosureValidWF_1682 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_1722 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.loc-mode
d_loc'45'mode_1724 :: T_ClosureValidWF_1682 -> AgdaAny
d_loc'45'mode_1724 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-at
d_env'45'at_1726 :: T_ClosureValidWF_1682 -> T_EnvAt_1648
d_env'45'at_1726 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_1728 ::
  T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1728 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1730 ::
  T_ClosureValidWF_1682 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_1730 v0
  = case coe v0 of
      C_constructor_1736 v1 v2 v3 v4 v5 v6 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1734 ::
  T_ClosureValidWF_1682 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1734 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_1752 ::
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
  T_ValidAtWF_616 -> T_ClosureValidWF_1682
d_decomposeClosureWF_1752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10
  = du_decomposeClosureWF_1752 v10
du_decomposeClosureWF_1752 ::
  T_ValidAtWF_616 -> T_ClosureValidWF_1682
du_decomposeClosureWF_1752 v0
  = case coe v0 of
      C_valid'45'closure'45'wf_882 v1 v4 v5 v8 v10 v11 v12 v15 v16 v17
        -> coe
             C_constructor_1736 v1 v4 v5 v11 v12
             (coe C_env'45'at'45'loc_1664 v10 v8 v15 v17) v16
      C_valid'45'closure'45'reg'45'wf_906 v1 v4 v5 v9 v10 v11 v14
        -> coe
             C_constructor_1736 v1 v4 v5 v9 v10
             (coe C_env'45'in'45'cell_1668 v11) v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.Place
d_Place_1796 a0 a1 a2 = ()
data T_Place_1796
  = C_AtStorage_1798 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_InReg_1800 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InputPlace
d_InputPlace_1812 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InputPlace_1812
  = C_in'45'at'45'loc_1826 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           T_ValidAtWF_616
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 |
    C_in'45'at'45'reg_1830 MAlonzo.Code.Once.IRTy.T_FitsInRegI_518 |
    C_in'45'unit_1832
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.input-sv
d_input'45'sv_1844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_InputPlace_1812 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_input'45'sv_1844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_input'45'sv_1844 v6 v7 v8
du_input'45'sv_1844 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_InputPlace_1812 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_input'45'sv_1844 v0 v1 v2
  = case coe v2 of
      C_in'45'at'45'loc_1826 v3 v4 v5
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3)
      C_in'45'at'45'reg_1830 v3
        -> coe du_prim'45'sv_582 (coe v3) (coe v0)
      C_in'45'unit_1832
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v1))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.input-read
d_input'45'read_1866 ::
  T_InputPlace_1812 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'read_1866 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_1872 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_RecDispatcherWF_1872 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF
d_PairValidWF_1906 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_PairValidWF_1906
  = C_constructor_1932 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                       T_CellAt_612 T_CellAt_612
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_1926 ::
  T_PairValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_1926 v0
  = case coe v0 of
      C_constructor_1932 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-cell
d_fst'45'cell_1928 :: T_PairValidWF_1906 -> T_CellAt_612
d_fst'45'cell_1928 v0
  = case coe v0 of
      C_constructor_1932 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-cell
d_snd'45'cell_1930 :: T_PairValidWF_1906 -> T_CellAt_612
d_snd'45'cell_1930 v0
  = case coe v0 of
      C_constructor_1932 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_1948 ::
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
  T_ValidAtWF_616 -> T_PairValidWF_1906
d_decomposePairWF_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_decomposePairWF_1948 v10
du_decomposePairWF_1948 :: T_ValidAtWF_616 -> T_PairValidWF_1906
du_decomposePairWF_1948 v0
  = case coe v0 of
      C_valid'45'pair'45'wf_856 v9 v10 v11 v12
        -> coe C_constructor_1932 (coe v10) (coe v11) (coe v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PayloadAt
d_PayloadAt_1968 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_PayloadAt_1968
  = C_payload'45'at'45'loc_1984 MAlonzo.Code.Once.IR.T_AllocMode_4
                                MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                                T_ValidAtWF_616 |
    C_payload'45'in'45'reg_1988 T_InlineRep_590
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.payload-sv
d_payload'45'sv_2000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_PayloadAt_1968 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_payload'45'sv_2000 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_payload'45'sv_2000 v5 v8
du_payload'45'sv_2000 ::
  AgdaAny ->
  T_PayloadAt_1968 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_payload'45'sv_2000 v0 v1
  = case coe v1 of
      C_payload'45'at'45'loc_1984 v2 v3 v5 v6
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3)
      C_payload'45'in'45'reg_1988 v2
        -> coe du_inline'45'sv_600 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.payload-read
d_payload'45'read_2020 ::
  T_PayloadAt_1968 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'read_2020 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF
d_InlValidWF_2038 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InlValidWF_2038
  = C_constructor_2068 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                       T_PayloadAt_1968
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.a
d_a_2060 :: T_InlValidWF_2038 -> AgdaAny
d_a_2060 v0
  = case coe v0 of
      C_constructor_2068 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_2062 ::
  T_InlValidWF_2038 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_2062 v0
  = case coe v0 of
      C_constructor_2068 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload
d_payload_2064 :: T_InlValidWF_2038 -> T_PayloadAt_1968
d_payload_2064 v0
  = case coe v0 of
      C_constructor_2068 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_2066 ::
  T_InlValidWF_2038 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_2066 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF
d_InrValidWF_2082 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InrValidWF_2082
  = C_constructor_2112 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
                       T_PayloadAt_1968
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.b
d_b_2104 :: T_InrValidWF_2082 -> AgdaAny
d_b_2104 v0
  = case coe v0 of
      C_constructor_2112 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_2106 ::
  T_InrValidWF_2082 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_sucLoc'45'before_2106 v0
  = case coe v0 of
      C_constructor_2112 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload
d_payload_2108 :: T_InrValidWF_2082 -> T_PayloadAt_1968
d_payload_2108 v0
  = case coe v0 of
      C_constructor_2112 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_2110 ::
  T_InrValidWF_2082 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_2110 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_2128 ::
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
  T_ValidAtWF_616 -> T_InlValidWF_2038
d_decomposeInlWF_2128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInlWF_2128 v7 v10
du_decomposeInlWF_2128 ::
  AgdaAny -> T_ValidAtWF_616 -> T_InlValidWF_2038
du_decomposeInlWF_2128 v0 v1
  = case coe v1 of
      C_valid'45'inl'45'wf_946 v8 v10 v11 v14 v15 v16
        -> coe
             C_constructor_2068 v0 v15
             (coe C_payload'45'at'45'loc_1984 v10 v8 v14 v16)
      C_valid'45'inl'45'reg'45'wf_984 v9 v11 v13
        -> coe
             C_constructor_2068 v0 v13 (coe C_payload'45'in'45'reg_1988 v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_2170 ::
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
  T_ValidAtWF_616 -> T_InrValidWF_2082
d_decomposeInrWF_2170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInrWF_2170 v7 v10
du_decomposeInrWF_2170 ::
  AgdaAny -> T_ValidAtWF_616 -> T_InrValidWF_2082
du_decomposeInrWF_2170 v0 v1
  = case coe v1 of
      C_valid'45'inr'45'wf_966 v8 v10 v11 v14 v15 v16
        -> coe
             C_constructor_2112 v0 v15
             (coe C_payload'45'at'45'loc_1984 v10 v8 v14 v16)
      C_valid'45'inr'45'reg'45'wf_1002 v9 v11 v13
        -> coe
             C_constructor_2112 v0 v13 (coe C_payload'45'in'45'reg_1988 v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_2206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_ValidAtWF_616
d_valid'45'to'45'validWF'45'unit_2206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_valid'45'to'45'validWF'45'unit_2206
du_valid'45'to'45'validWF'45'unit_2206 :: T_ValidAtWF_616
du_valid'45'to'45'validWF'45'unit_2206
  = coe C_valid'45'unit'45'wf_838
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_2222 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'mem'45'only_2222 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9
                                 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'only_2222 v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'only_2222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'mem'45'only_2222 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_valid'45'pair'45'wf_856 v17 v18
                           (coe
                              du_go_2270 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v21) (coe v23) (coe v19))
                           (coe
                              du_go_2270 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v22) (coe v24) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_ev''_2326 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v9) (coe v13) (coe v16) (coe v18) (coe v25))
      C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
      C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18
             (coe
                du_go_2390 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v10) (coe v13) (coe v19))
             v21
      C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_2498 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v24) (coe v26) (coe v15) (coe v17) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_2538 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v25) (coe v26) (coe v15) (coe v17) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
        -> coe C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
      C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
        -> coe C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
      C_valid'45'μ'45'wf_1018 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_valid'45'μ'45'wf_1018 v14
                    (coe
                       du_validityWF'45'mem'45'only_2222 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v14) v5))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v14 -> coe C_valid'45'int'45'wf_1030 v14
      C_valid'45'float'45'wf_1042 v14
        -> coe C_valid'45'float'45'wf_1042 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_2270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_2270 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 v21
  = du_go_2270 v0 v1 v2 v4 v6 v7 v18 v19 v21
du_go_2270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_2270 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'mem'45'only_2222 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2322 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2324 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2324 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_2326 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_ev''_2326 v0 v1 v2 v3 v5 v6 v9 v13 v14 v15 v22
du_ev''_2326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_2326 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2222 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_2390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_2390 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20 ~v21 v22
  = du_go_2390 v0 v1 v2 v3 v5 v6 v19 v20 v22
du_go_2390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_2390 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'mem'45'only_2222 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_2494 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2496 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_2498 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2498 v0 v1 v2 v4 v6 v7 v10 v12 v13 v14 v20
du_pv''_2498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_2498 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2222 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_2534 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2536 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_2538 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2538 v0 v1 v2 v4 v6 v7 v11 v12 v13 v14 v20
du_pv''_2538 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_2538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2222 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_2610 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'write'45'at'45'frontier_2610 v0 v1 v2 ~v3 v4 v5 v6
                                             ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'frontier_2610
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'frontier_2610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'write'45'at'45'frontier_2610 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8
  = case coe v8 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_valid'45'pair'45'wf_856 v17 v18
                           (coe
                              du_go_2654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v21) (coe v23) (coe v19))
                           (coe
                              du_go_2654 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v22) (coe v24) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_ev''_2712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v9) (coe v13) (coe v16) (coe v18) (coe v23) (coe v25))
      C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
      C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18
             (coe
                du_go_2772 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v10) (coe v13) (coe v19))
             v21
      C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_2878 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v24) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_2916 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v25) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
        -> coe C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
      C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
        -> coe C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
      C_valid'45'μ'45'wf_1018 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_valid'45'μ'45'wf_1018 v14
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2610 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v14) v5))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v14 -> coe C_valid'45'int'45'wf_1030 v14
      C_valid'45'float'45'wf_1042 v14
        -> coe C_valid'45'float'45'wf_1042 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_2654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_2654 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21
  = du_go_2654 v0 v1 v2 v4 v6 v7 v17 v18 v21
du_go_2654 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_2654 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'at'45'frontier_2610 (coe v0) (coe v1)
                (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2708 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2710 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_2712 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21
  = du_ev''_2712 v0 v1 v2 v3 v5 v6 v8 v12 v13 v14 v19 v21
du_ev''_2712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_2712 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2610 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_2772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_2772 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 v22
  = du_go_2772 v0 v1 v2 v3 v5 v6 v18 v19 v22
du_go_2772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_2772 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'at'45'frontier_2610 (coe v0) (coe v1)
                (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2874 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_2874 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2876 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2876 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_2878 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2878 v0 v1 v2 v4 v6 v7 v9 v11 v12 v13 v17 v19
du_pv''_2878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_2878 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2610 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2912 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_2912 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2914 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2914 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_2916 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2916 v0 v1 v2 v4 v6 v7 v10 v11 v12 v13 v17 v19
du_pv''_2916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_2916 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2610 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_2982 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'write'45'at'45'suc'45'frontier_2982 v0 v1 v2 ~v3 v4
                                                    v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'suc'45'frontier_2982
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'suc'45'frontier_2982 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'write'45'at'45'suc'45'frontier_2982 v0 v1 v2 v3 v4
                                                     v5 v6 v7 v8
  = case coe v8 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_valid'45'pair'45'wf_856 v17 v18
                           (coe
                              du_go_3026 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v21) (coe v23) (coe v19))
                           (coe
                              du_go_3026 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v22) (coe v24) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_ev''_3084 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v9) (coe v13) (coe v16) (coe v18) (coe v23) (coe v25))
      C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
      C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18
             (coe
                du_go_3144 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v10) (coe v13) (coe v19))
             v21
      C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_3250 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v24) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_3288 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v25) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
        -> coe C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
      C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
        -> coe C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
      C_valid'45'μ'45'wf_1018 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_valid'45'μ'45'wf_1018 v14
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2982 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v14) v5))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v14 -> coe C_valid'45'int'45'wf_1030 v14
      C_valid'45'float'45'wf_1042 v14
        -> coe C_valid'45'float'45'wf_1042 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_3026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_3026 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21
  = du_go_3026 v0 v1 v2 v4 v6 v7 v17 v18 v21
du_go_3026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_3026 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'at'45'suc'45'frontier_2982 (coe v0)
                (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
                (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_3080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_3080 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_3082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_3082 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_3084 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21
  = du_ev''_3084 v0 v1 v2 v3 v5 v6 v8 v12 v13 v14 v19 v21
du_ev''_3084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_3084 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2982 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_3144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_3144 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 v22
  = du_go_3144 v0 v1 v2 v3 v5 v6 v18 v19 v22
du_go_3144 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_3144 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'at'45'suc'45'frontier_2982 (coe v0)
                (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
                (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_3246 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3248 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_3250 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3250 v0 v1 v2 v4 v6 v7 v9 v11 v12 v13 v17 v19
du_pv''_3250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_3250 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2982 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_3284 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3286 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3286 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_3288 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3288 v0 v1 v2 v4 v6 v7 v10 v11 v12 v13 v17 v19
du_pv''_3288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_3288 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2982 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-sv-at-frontier
d_validityWF'45'write'45'sv'45'at'45'frontier_3354 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'write'45'sv'45'at'45'frontier_3354 v0 v1 v2 ~v3 v4
                                                   v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'sv'45'at'45'frontier_3354
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'sv'45'at'45'frontier_3354 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'write'45'sv'45'at'45'frontier_3354 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = case coe v8 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_valid'45'pair'45'wf_856 v17 v18
                           (coe
                              du_go_3398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v21) (coe v23) (coe v19))
                           (coe
                              du_go_3398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v22) (coe v24) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_ev''_3456 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v9) (coe v13) (coe v16) (coe v18) (coe v23) (coe v25))
      C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
      C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18
             (coe
                du_go_3516 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v10) (coe v13) (coe v19))
             v21
      C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_3622 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v24) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_3660 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v25) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
        -> coe C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
      C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
        -> coe C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
      C_valid'45'μ'45'wf_1018 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_valid'45'μ'45'wf_1018 v14
                    (coe
                       du_validityWF'45'write'45'sv'45'at'45'frontier_3354 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v14) v5))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v14 -> coe C_valid'45'int'45'wf_1030 v14
      C_valid'45'float'45'wf_1042 v14
        -> coe C_valid'45'float'45'wf_1042 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_3398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_3398 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21
  = du_go_3398 v0 v1 v2 v4 v6 v7 v17 v18 v21
du_go_3398 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_3398 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'sv'45'at'45'frontier_3354 (coe v0)
                (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
                (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_3452 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_3452 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_3454 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_3454 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_3456 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21
  = du_ev''_3456 v0 v1 v2 v3 v5 v6 v8 v12 v13 v14 v19 v21
du_ev''_3456 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_3456 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3354 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_3516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_3516 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 v22
  = du_go_3516 v0 v1 v2 v3 v5 v6 v18 v19 v22
du_go_3516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_3516 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'sv'45'at'45'frontier_3354 (coe v0)
                (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
                (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_3618 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3620 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3620 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_3622 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3622 v0 v1 v2 v4 v6 v7 v9 v11 v12 v13 v17 v19
du_pv''_3622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_3622 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3354 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3656 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_3656 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3658 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_3660 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3660 v0 v1 v2 v4 v6 v7 v10 v11 v12 v13 v17 v19
du_pv''_3660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_3660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3354 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-sv-at-suc-frontier
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 v0 v1 v2
                                                          ~v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 v0 v1 v2
                                                           v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_valid'45'pair'45'wf_856 v17 v18
                           (coe
                              du_go_3770 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v21) (coe v23) (coe v19))
                           (coe
                              du_go_3770 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v22) (coe v24) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_ev''_3828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v9) (coe v13) (coe v16) (coe v18) (coe v23) (coe v25))
      C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
      C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18
             (coe
                du_go_3888 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v10) (coe v13) (coe v19))
             v21
      C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_3994 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v24) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_4032 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v25) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
        -> coe C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
      C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
        -> coe C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
      C_valid'45'μ'45'wf_1018 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_valid'45'μ'45'wf_1018 v14
                    (coe
                       du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v14) v5))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v14 -> coe C_valid'45'int'45'wf_1030 v14
      C_valid'45'float'45'wf_1042 v14
        -> coe C_valid'45'float'45'wf_1042 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_3770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_3770 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21
  = du_go_3770 v0 v1 v2 v4 v6 v7 v17 v18 v21
du_go_3770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_3770 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 (coe v0)
                (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
                (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_3824 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_3824 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_3826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_3826 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_3828 v0 v1 v2 v3 ~v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21
  = du_ev''_3828 v0 v1 v2 v3 v5 v6 v8 v12 v13 v14 v19 v21
du_ev''_3828 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_3828 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_3888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_3888 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 v22
  = du_go_3888 v0 v1 v2 v3 v5 v6 v18 v19 v22
du_go_3888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_3888 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 (coe v0)
                (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
                (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_3990 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3992 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3992 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_3994 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3994 v0 v1 v2 v4 v6 v7 v9 v11 v12 v13 v17 v19
du_pv''_3994 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_3994 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_4028 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4030 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4030 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_4032 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_4032 v0 v1 v2 v4 v6 v7 v10 v11 v12 v13 v17 v19
du_pv''_4032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_4032 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3726 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_4100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer -> T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'alloc'45'advance_4100 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
                                      v9 v10
  = du_validityWF'45'alloc'45'advance_4100
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10
du_validityWF'45'alloc'45'advance_4100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer -> T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'alloc'45'advance_4100 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = case coe v9 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v22 v23
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                      -> coe
                           C_valid'45'pair'45'wf_856 v18
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                              (coe v3)
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                              (coe v19))
                           (coe
                              du_go_4140 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                              (coe v22) (coe v24) (coe v20))
                           (coe
                              du_go_4140 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                              (coe v23) (coe v25) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v10 v13 v14 v17 v19 v20 v21 v24 v25 v26
        -> coe
             C_valid'45'closure'45'wf_882 v10 v13 v14 v17 v19 v20 v21
             (coe du_eb''_4188 (coe v3) (coe v17) (coe v24))
             (coe du_slb''_4190 (coe v3) (coe v6) (coe v25))
             (coe
                du_ev''_4192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                (coe v10) (coe v14) (coe v17) (coe v19) (coe v26))
      C_valid'45'closure'45'reg'45'wf_906 v10 v13 v14 v18 v19 v20 v23
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v10 v13 v14 v18 v19 v20
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                (coe v23))
      C_valid'45'ν'45'susp'45'wf_926 v11 v12 v13 v14 v18 v19 v20 v22
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v11 v12 v13 v14 v18 v19
             (coe
                du_go_4248 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                (coe v11) (coe v14) (coe v20))
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                (coe v22))
      C_valid'45'inl'45'wf_946 v16 v18 v19 v22 v23 v24
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v27
                      -> coe
                           C_valid'45'inl'45'wf_946 v16 v18 v19
                           (coe du_pb''_4340 (coe v3) (coe v16) (coe v22))
                           (coe du_slb''_4342 (coe v3) (coe v6) (coe v23))
                           (coe
                              du_pv''_4344 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                              (coe v25) (coe v27) (coe v16) (coe v18) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v16 v18 v19 v22 v23 v24
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v27
                      -> coe
                           C_valid'45'inr'45'wf_966 v16 v18 v19
                           (coe du_pb''_4376 (coe v3) (coe v16) (coe v22))
                           (coe du_slb''_4378 (coe v3) (coe v6) (coe v23))
                           (coe
                              du_pv''_4380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                              (coe v26) (coe v27) (coe v16) (coe v18) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v17 v19 v21
        -> coe
             C_valid'45'inl'45'reg'45'wf_984 v17 v19
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                (coe v21))
      C_valid'45'inr'45'reg'45'wf_1002 v17 v19 v21
        -> coe
             C_valid'45'inr'45'reg'45'wf_1002 v17 v19
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                (coe v21))
      C_valid'45'μ'45'wf_1018 v15 v17
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v18
               -> coe
                    C_valid'45'μ'45'wf_1018 v15
                    (coe
                       du_validityWF'45'alloc'45'advance_4100 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v18) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v18) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v15) v5))
                       (coe v6) (coe v7) (coe v8) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v15
        -> coe
             C_valid'45'int'45'wf_1030
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3) (coe v6) (coe v15))
      C_valid'45'float'45'wf_1042 v15
        -> coe
             C_valid'45'float'45'wf_1042
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3) (coe v6) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_4140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_4140 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 v16 v17 ~v18 v19
  = du_go_4140 v0 v1 v2 v4 v6 v7 v16 v17 v19
du_go_4140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_4140 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3) (coe v12) (coe v16))
             (coe
                du_validityWF'45'alloc'45'advance_4100 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6) (coe v7) (coe v12) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_4188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_eb''_4188 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20
  = du_eb''_4188 v3 v12 v18
du_eb''_4188 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_eb''_4188 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_slb''_4190 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_slb''_4190 v3 v4 v19
du_slb''_4190 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_slb''_4190 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_4192 v0 v1 v2 v3 ~v4 v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_ev''_4192 v0 v1 v2 v3 v5 v6 v7 v11 v12 v13 v20
du_ev''_4192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_4192 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4100 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v8) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_4248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_4248 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 v17 v18 ~v19 v20
  = du_go_4248 v0 v1 v2 v3 v5 v6 v17 v18 v20
du_go_4248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_4248 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
                (coe v3) (coe v12) (coe v16))
             (coe
                du_validityWF'45'alloc'45'advance_4100 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6) (coe v7) (coe v12) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_pb''_4340 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_4340 v4 v11 v16
du_pb''_4340 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_pb''_4340 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_slb''_4342 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_4342 v4 v5 v17
du_slb''_4342 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_slb''_4342 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_4344 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_4344 v0 v1 v2 v4 v6 v7 v8 v10 v11 v12 v18
du_pv''_4344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_4344 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4100 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v8) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_pb''_4376 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_4376 v4 v11 v16
du_pb''_4376 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_pb''_4376 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4378 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_slb''_4378 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_4378 v4 v5 v17
du_slb''_4378 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_slb''_4378 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_798
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_4380 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_4380 v0 v1 v2 v4 v6 v7 v9 v10 v11 v12 v18
du_pv''_4380 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_4380 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4100 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v8) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_4440 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'frontier'45'advance_4440 v0 v1 v2 ~v3 v4 v5 v6 v7
                                         v8 v9 ~v10 v11 v12 v13
  = du_validityWF'45'frontier'45'advance_4440
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_validityWF'45'frontier'45'advance_4440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'frontier'45'advance_4440 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 v11
  = case coe v11 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v20 v21 v22 v23
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v24 v25
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                      -> coe
                           C_valid'45'pair'45'wf_856 v20
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                              (coe v9) (coe v10)
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                              (coe v21))
                           (coe
                              du_go_4492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                              (coe v9) (coe v10) (coe v24) (coe v26) (coe v22))
                           (coe
                              du_go_4492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                              (coe v9) (coe v10) (coe v25) (coe v27) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v12 v15 v16 v19 v21 v22 v23 v26 v27 v28
        -> coe
             C_valid'45'closure'45'wf_882 v12 v15 v16 v19 v21 v22 v23
             (coe du_eb''_4546 (coe v9) (coe v10) (coe v19) (coe v26))
             (coe du_slb''_4548 (coe v7) (coe v9) (coe v10) (coe v27))
             (coe
                du_ev''_4550 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                (coe v9) (coe v10) (coe v12) (coe v16) (coe v19) (coe v21)
                (coe v28))
      C_valid'45'closure'45'reg'45'wf_906 v12 v15 v16 v20 v21 v22 v25
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v12 v15 v16 v20 v21 v22
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                (coe v25))
      C_valid'45'ν'45'susp'45'wf_926 v13 v14 v15 v16 v20 v21 v22 v24
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v13 v14 v15 v16 v20 v21
             (coe
                du_go_4618 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                (coe v9) (coe v10) (coe v13) (coe v16) (coe v22))
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                (coe v24))
      C_valid'45'inl'45'wf_946 v18 v20 v21 v24 v25 v26
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                      -> coe
                           C_valid'45'inl'45'wf_946 v18 v20 v21
                           (coe du_pb''_4728 (coe v9) (coe v10) (coe v18) (coe v24))
                           (coe du_slb''_4730 (coe v7) (coe v9) (coe v10) (coe v25))
                           (coe
                              du_pv''_4732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                              (coe v9) (coe v10) (coe v27) (coe v29) (coe v18) (coe v20)
                              (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v18 v20 v21 v24 v25 v26
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                      -> coe
                           C_valid'45'inr'45'wf_966 v18 v20 v21
                           (coe du_pb''_4770 (coe v9) (coe v10) (coe v18) (coe v24))
                           (coe du_slb''_4772 (coe v7) (coe v9) (coe v10) (coe v25))
                           (coe
                              du_pv''_4774 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                              (coe v9) (coe v10) (coe v28) (coe v29) (coe v18) (coe v20)
                              (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v19 v21 v23
        -> coe
             C_valid'45'inl'45'reg'45'wf_984 v19 v21
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                (coe v23))
      C_valid'45'inr'45'reg'45'wf_1002 v19 v21 v23
        -> coe
             C_valid'45'inr'45'reg'45'wf_1002 v19 v21
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v9) (coe v10)
                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                (coe v23))
      C_valid'45'μ'45'wf_1018 v17 v19
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v20
               -> coe
                    C_valid'45'μ'45'wf_1018 v17
                    (coe
                       du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v20) (coe v5))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v5
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v20) (coe v5))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v17) v6))
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v17
        -> coe
             C_valid'45'int'45'wf_1030
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v9) (coe v10) (coe v7) (coe v17))
      C_valid'45'float'45'wf_1042 v17
        -> coe
             C_valid'45'float'45'wf_1042
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v9) (coe v10) (coe v7) (coe v17))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_4492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_4492 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 ~v12 ~v13 ~v14
          ~v15 ~v16 ~v17 ~v18 v19 v20 ~v21 v22
  = du_go_4492 v0 v1 v2 v4 v5 v7 v9 v10 v19 v20 v22
du_go_4492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_4492 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_cell'45'ptr_816 v14 v16 v18 v19
        -> coe
             C_cell'45'ptr_816 v14 v16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v6) (coe v7) (coe v14) (coe v18))
             (coe
                du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
                (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v14) (coe v5)
                (coe v6) (coe v7) (coe v19))
      C_cell'45'inline_828 v15 -> coe C_cell'45'inline_828 v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_4546 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_eb''_4546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
            ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_eb''_4546 v8 v9 v15 v21
du_eb''_4546 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_eb''_4546 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_slb''_4548 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_slb''_4548 v5 v8 v9 v22
du_slb''_4548 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_slb''_4548 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_4550 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 v9 v10 ~v11 ~v12 ~v13 v14
            v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_ev''_4550 v0 v1 v2 v3 v4 v6 v8 v9 v10 v14 v15 v16 v23
du_ev''_4550 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_4550 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v10) (coe v5)
      (coe v6) (coe v7) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_4618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_4618 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14
          ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 ~v22 v23
  = du_go_4618 v0 v1 v2 v3 v4 v6 v8 v9 v20 v21 v23
du_go_4618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_4618 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_cell'45'ptr_816 v14 v16 v18 v19
        -> coe
             C_cell'45'ptr_816 v14 v16
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v6) (coe v7) (coe v14) (coe v18))
             (coe
                du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
                (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v14) (coe v5)
                (coe v6) (coe v7) (coe v19))
      C_cell'45'inline_828 v15 -> coe C_cell'45'inline_828 v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_pb''_4728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_4728 v9 v10 v14 v19
du_pb''_4728 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_pb''_4728 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_slb''_4730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_4730 v6 v9 v10 v20
du_slb''_4730 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_slb''_4730 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4732 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_4732 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10 v11 ~v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_4732 v0 v1 v2 v4 v5 v7 v9 v10 v11 v13 v14 v15 v21
du_pv''_4732 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_4732 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v10) (coe v5)
      (coe v6) (coe v7) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4770 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_pb''_4770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 ~v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_4770 v9 v10 v14 v19
du_pb''_4770 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_pb''_4770 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4772 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_slb''_4772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_4772 v6 v9 v10 v20
du_slb''_4772 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_slb''_4772 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_4774 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_4774 v0 v1 v2 v4 v5 v7 v9 v10 v12 v13 v14 v15 v21
du_pv''_4774 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_4774 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v10) (coe v5)
      (coe v6) (coe v7) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_4856 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'with'45'bf'45'transfer_4856 v0 v1 v2 ~v3 v4 v5 v6
                                            v7 v8 v9 v10 v11
  = du_validityWF'45'with'45'bf'45'transfer_4856
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_validityWF'45'with'45'bf'45'transfer_4856 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'with'45'bf'45'transfer_4856 v0 v1 v2 v3 v4 v5 v6
                                             v7 v8 v9 v10
  = case coe v10 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v19 v20 v21 v22
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                      -> coe
                           C_valid'45'pair'45'wf_856 v19
                           (coe
                              v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                              v20)
                           (coe
                              du_go_4900 (coe v0) (coe v1) (coe v2) (coe v6) (coe v7) (coe v8)
                              (coe v9) (coe v23) (coe v25) (coe v21))
                           (coe
                              du_go_4900 (coe v0) (coe v1) (coe v2) (coe v6) (coe v7) (coe v8)
                              (coe v9) (coe v24) (coe v26) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v11 v14 v15 v18 v20 v21 v22 v25 v26 v27
        -> coe
             C_valid'45'closure'45'wf_882 v11 v14 v15 v18 v20 v21 v22
             (coe v9 v18 v25)
             (coe
                v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                v26)
             (coe
                du_validityWF'45'with'45'bf'45'transfer_4856 (coe v0) (coe v1)
                (coe v2) (coe v11) (coe v15) (coe v18) (coe v6) (coe v7) (coe v8)
                (coe v9) (coe v27))
      C_valid'45'closure'45'reg'45'wf_906 v11 v14 v15 v19 v20 v21 v24
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v11 v14 v15 v19 v20 v21
             (coe
                v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                v24)
      C_valid'45'ν'45'susp'45'wf_926 v12 v13 v14 v15 v19 v20 v21 v23
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v12 v13 v14 v15 v19 v20
             (coe
                du_go_5004 (coe v0) (coe v1) (coe v2) (coe v6) (coe v7) (coe v8)
                (coe v9) (coe v12) (coe v15) (coe v21))
             (coe
                v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                v23)
      C_valid'45'inl'45'wf_946 v17 v19 v20 v23 v24 v25
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v26 v27
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v28
                      -> coe
                           C_valid'45'inl'45'wf_946 v17 v19 v20 (coe v9 v17 v23)
                           (coe
                              v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                              v24)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_4856 (coe v0) (coe v1)
                              (coe v2) (coe v26) (coe v28) (coe v17) (coe v6) (coe v7) (coe v8)
                              (coe v9) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v17 v19 v20 v23 v24 v25
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v26 v27
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v28
                      -> coe
                           C_valid'45'inr'45'wf_966 v17 v19 v20 (coe v9 v17 v23)
                           (coe
                              v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                              v24)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_4856 (coe v0) (coe v1)
                              (coe v2) (coe v27) (coe v28) (coe v17) (coe v6) (coe v7) (coe v8)
                              (coe v9) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v18 v20 v22
        -> coe
             C_valid'45'inl'45'reg'45'wf_984 v18 v20
             (coe
                v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                v22)
      C_valid'45'inr'45'reg'45'wf_1002 v18 v20 v22
        -> coe
             C_valid'45'inr'45'reg'45'wf_1002 v18 v20
             (coe
                v9 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v5))
                v22)
      C_valid'45'μ'45'wf_1018 v16 v18
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v19
               -> coe
                    C_valid'45'μ'45'wf_1018 v16
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_4856 (coe v0) (coe v1)
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v19) (coe v3))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v3
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v19) (coe v3))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v16) v4))
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v16
        -> coe C_valid'45'int'45'wf_1030 (coe v9 v5 v16)
      C_valid'45'float'45'wf_1042 v16
        -> coe C_valid'45'float'45'wf_1042 (coe v9 v5 v16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_4900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_4900 v0 v1 v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
          ~v15 ~v16 v17 v18 ~v19 v20
  = du_go_4900 v0 v1 v2 v5 v6 v7 v8 v17 v18 v20
du_go_4900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_4900 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_cell'45'ptr_816 v13 v15 v17 v18
        -> coe
             C_cell'45'ptr_816 v13 v15 (coe v6 v13 v17)
             (coe
                du_validityWF'45'with'45'bf'45'transfer_4856 (coe v0) (coe v1)
                (coe v2) (coe v7) (coe v8) (coe v13) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v18))
      C_cell'45'inline_828 v14 -> coe C_cell'45'inline_828 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_5004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_CellAt_612 -> T_CellAt_612
d_go_5004 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
          ~v15 ~v16 ~v17 v18 v19 ~v20 v21
  = du_go_5004 v0 v1 v2 v4 v5 v6 v7 v18 v19 v21
du_go_5004 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_5004 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_cell'45'ptr_816 v13 v15 v17 v18
        -> coe
             C_cell'45'ptr_816 v13 v15 (coe v6 v13 v17)
             (coe
                du_validityWF'45'with'45'bf'45'transfer_4856 (coe v0) (coe v1)
                (coe v2) (coe v7) (coe v8) (coe v13) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v18))
      C_cell'45'inline_828 v14 -> coe C_cell'45'inline_828 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_5192 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'mem'45'preserved_5192 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8
                                      v9 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'preserved_5192
      v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'preserved_5192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'mem'45'preserved_5192 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_valid'45'pair'45'wf_856 v17 v18
                           (coe
                              du_go_5240 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v21) (coe v23) (coe v19))
                           (coe
                              du_go_5240 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v22) (coe v24) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_valid'45'closure'45'wf_882 v9 v12 v13 v16 v18 v19 v20 v23 v24
             (coe
                du_ev''_5300 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v9) (coe v13) (coe v16) (coe v18) (coe v23) (coe v25))
      C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
        -> coe
             C_valid'45'closure'45'reg'45'wf_906 v9 v12 v13 v17 v18 v19 v22
      C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_valid'45'ν'45'susp'45'wf_926 v10 v11 v12 v13 v17 v18
             (coe
                du_go_5364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                (coe v10) (coe v13) (coe v19))
             v21
      C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_946 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_5476 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v24) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_966 v15 v17 v18 v21 v22
                           (coe
                              du_pv''_5516 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                              (coe v25) (coe v26) (coe v15) (coe v17) (coe v21) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
        -> coe C_valid'45'inl'45'reg'45'wf_984 v16 v18 v20
      C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
        -> coe C_valid'45'inr'45'reg'45'wf_1002 v16 v18 v20
      C_valid'45'μ'45'wf_1018 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_valid'45'μ'45'wf_1018 v14
                    (coe
                       du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_1052
                          (coe du_ι'7584'_26 (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_eval'7472'_24 v1 v2 v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v14) v5))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v14 -> coe C_valid'45'int'45'wf_1030 v14
      C_valid'45'float'45'wf_1042 v14
        -> coe C_valid'45'float'45'wf_1042 v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_5240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_5240 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 ~v21 v22
  = du_go_5240 v0 v1 v2 v4 v6 v7 v18 v19 v22
du_go_5240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_5240 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_5296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_5296 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_5298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_5298 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_5300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_ev''_5300 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 v22
  = du_ev''_5300 v0 v1 v2 v3 v5 v6 v9 v13 v14 v15 v20 v22
du_ev''_5300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_ev''_5300 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_5364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 -> T_CellAt_612
d_go_5364 v0 v1 v2 v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20 ~v21 ~v22 v23
  = du_go_5364 v0 v1 v2 v3 v5 v6 v19 v20 v23
du_go_5364 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> T_CellAt_612
du_go_5364 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_cell'45'ptr_816 v12 v14 v16 v17
        -> coe
             C_cell'45'ptr_816 v12 v14 v16
             (coe
                du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v17))
      C_cell'45'inline_828 v13 -> coe C_cell'45'inline_828 v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_5472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_5472 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_5474 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_5474 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_5476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_5476 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_5476 v0 v1 v2 v4 v6 v7 v10 v12 v13 v14 v18 v20
du_pv''_5476 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_5476 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_5512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny
d_tg''_5512 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_5514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_5514 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_5516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_pv''_5516 v0 v1 v2 ~v3 v4 ~v5 v6 v7 ~v8 ~v9 ~v10 v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_5516 v0 v1 v2 v4 v6 v7 v11 v12 v13 v14 v18 v20
du_pv''_5516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_pv''_5516 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.inputPlace-transport
d_inputPlace'45'transport_5592 ::
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
  T_InputPlace_1812 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputPlace_1812
d_inputPlace'45'transport_5592 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10
                               ~v11 v12 v13 ~v14 ~v15
  = du_inputPlace'45'transport_5592
      v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v12 v13
du_inputPlace'45'transport_5592 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_InputPlace_1812 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_InputPlace_1812
du_inputPlace'45'transport_5592 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11
  = case coe v9 of
      C_in'45'at'45'loc_1826 v12 v13 v14
        -> coe
             C_in'45'at'45'loc_1826 v12
             (coe
                du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
                (coe v2) (coe v4) (coe v5) (coe v3) (coe v6) (coe v12) (coe v8)
                (coe v10) (coe v11)
                (coe
                   du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
                   (coe v4) (coe v3) (coe v6) (coe v7) (coe v8) (coe v13)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_868
                (coe v10) (coe v11) (coe v12) (coe v14))
      C_in'45'at'45'reg_1830 v12 -> coe C_in'45'at'45'reg_1830 v12
      C_in'45'unit_1832 -> coe C_in'45'unit_1832
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_5646
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-excluding"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocInRegions
d_LocInRegions_5654 a0 a1 a2 a3 a4 a5 a6 = ()
data T_LocInRegions_5654
  = C_loc'45'in'45'input_5664 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'fresh_5668 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'anc_5674 AgdaAny | C_loc'45'in'45'heap_5678
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.CellLocsInRegions
d_CellLocsInRegions_5694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> Integer -> T_CellAt_612 -> ()
d_CellLocsInRegions_5694 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_5712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> Integer -> T_ValidAtWF_616 -> ()
d_LocsInRegions_5712 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_5912 ::
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
  T_LocInRegions_5654 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_5912 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_5984
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\956-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_6010
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\957-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042 ::
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
  T_ValidAtWF_616 -> AgdaAny -> T_ValidAtWF_616
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042 v0
                                                                 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18
                                                                 v19 v20
  = du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v19 v20
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042 ::
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
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_616 -> AgdaAny -> T_ValidAtWF_616
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                  v12 v13 v14 v15
  = case coe v14 of
      C_valid'45'unit'45'wf_838 -> coe C_valid'45'unit'45'wf_838
      C_valid'45'pair'45'wf_856 v24 v25 v26 v27
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v28 v29
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                             -> case coe v33 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                    -> case coe v35 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                           -> coe
                                                C_valid'45'pair'45'wf_856 v24 v25
                                                (coe
                                                   du_go_6112 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v28) (coe v30) (coe v26)
                                                   (coe v36))
                                                (coe
                                                   du_go_6112 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v29) (coe v31) (coe v27)
                                                   (coe v37))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_882 v16 v19 v20 v23 v25 v26 v27 v30 v31 v32
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
               -> case coe v34 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                      -> coe
                           C_valid'45'closure'45'wf_882 v16 v19 v20 v23 v25 v26 v27 v30 v31
                           (coe
                              du_ev''_6200 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8) (coe v9)
                              (coe v10) (coe v11) (coe v12) (coe v13) (coe v16) (coe v20)
                              (coe v23) (coe v25) (coe v30) (coe v32) (coe v36))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'reg'45'wf_906 v16 v19 v20 v24 v25 v26 v29
        -> coe
             seq (coe v15)
             (coe
                C_valid'45'closure'45'reg'45'wf_906 v16 v19 v20 v24 v25 v26 v29)
      C_valid'45'ν'45'susp'45'wf_926 v17 v18 v19 v20 v24 v25 v26 v28
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
               -> case coe v30 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                      -> coe
                           C_valid'45'ν'45'susp'45'wf_926 v17 v18 v19 v20 v24 v25
                           (coe
                              du_go_6304 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8) (coe v9)
                              (coe v10) (coe v11) (coe v12) (coe v13) (coe v17) (coe v20)
                              (coe v26) (coe v32))
                           v28
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'wf_946 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inl'45'wf_946 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_6470 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v31) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_966 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inr'45'wf_966 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_6530 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v32) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_984 v23 v25 v27
        -> coe
             seq (coe v15) (coe C_valid'45'inl'45'reg'45'wf_984 v23 v25 v27)
      C_valid'45'inr'45'reg'45'wf_1002 v23 v25 v27
        -> coe
             seq (coe v15) (coe C_valid'45'inr'45'reg'45'wf_1002 v23 v25 v27)
      C_valid'45'μ'45'wf_1018 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v24
               -> coe
                    C_valid'45'μ'45'wf_1018 v21
                    (coe
                       d_μ'45'validity'45'in'45'regions'45'stub_5984 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_1030 v21 -> coe C_valid'45'int'45'wf_1030 v21
      C_valid'45'float'45'wf_1042 v21
        -> coe C_valid'45'float'45'wf_1042 v21
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_6112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_CellAt_612 ->
  T_CellAt_612 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CellAt_612 -> AgdaAny -> T_CellAt_612
d_go_6112 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
          ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 ~v27
          ~v28 v29 v30 ~v31 ~v32 v33 v34
  = du_go_6112 v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v29 v30 v33 v34
du_go_6112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> AgdaAny -> T_CellAt_612
du_go_6112 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      C_cell'45'ptr_816 v17 v19 v21 v22
        -> coe
             C_cell'45'ptr_816 v17 v19 v21
             (coe
                du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
                (coe v0) (coe v1) (coe v2) (coe v19) (coe v10) (coe v3) (coe v11)
                (coe v17) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                (coe v22) (coe v13))
      C_cell'45'inline_828 v18 -> coe C_cell'45'inline_828 v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cl-eq
d_cl'45'eq_6192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cl'45'eq_6192 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.scl-eq
d_scl'45'eq_6194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scl'45'eq_6194 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_6196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_6196 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_6198 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_6198 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_6200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 -> AgdaAny -> T_ValidAtWF_616
d_ev''_6200 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 v16 ~v17 ~v18 ~v19 v20 v21 v22 ~v23 ~v24 ~v25 ~v26 v27 ~v28
            v29 ~v30 ~v31 v32
  = du_ev''_6200
      v0 v1 v2 v3 v5 v6 v7 v8 v10 v11 v16 v20 v21 v22 v27 v29 v32
du_ev''_6200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny -> T_ValidAtWF_616
du_ev''_6200 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.go
d_go_6304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  T_CellAt_612 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CellAt_612 -> AgdaAny -> T_CellAt_612
d_go_6304 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
          ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 ~v26 ~v27
          ~v28 v29 v30 ~v31 ~v32 v33 v34
  = du_go_6304 v0 v1 v2 v3 v5 v6 v7 v8 v10 v11 v29 v30 v33 v34
du_go_6304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> T_CellAt_612 -> AgdaAny -> T_CellAt_612
du_go_6304 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v12 of
      C_cell'45'ptr_816 v17 v19 v21 v22
        -> coe
             C_cell'45'ptr_816 v17 v19 v21
             (coe
                du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
                (coe v0) (coe v1) (coe v2) (coe v19) (coe v10) (coe v3) (coe v11)
                (coe v17) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                (coe v22) (coe v13))
      C_cell'45'inline_828 v18 -> coe C_cell'45'inline_828 v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_6464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 -> T_LocInRegions_5654 -> AgdaAny -> AgdaAny
d_tg''_6464 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_6466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_6466 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_6468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_6468 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_6470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 -> AgdaAny -> T_ValidAtWF_616
d_pv''_6470 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_6470
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v20 v21 v25 v27 v30
du_pv''_6470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny -> T_ValidAtWF_616
du_pv''_6470 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_6524 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 -> T_LocInRegions_5654 -> AgdaAny -> AgdaAny
d_tg''_6524 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_6526 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_6526 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_6528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_6528 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_6530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 ->
  T_LocInRegions_5654 ->
  T_LocInRegions_5654 -> AgdaAny -> T_ValidAtWF_616
d_pv''_6530 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_6530
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v19 v20 v21 v25 v27 v30
du_pv''_6530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  T_ValidAtWF_616 -> AgdaAny -> T_ValidAtWF_616
du_pv''_6530 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_6042
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_6636
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_6642 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_reclaim'45'alloc_6642 ~v0 ~v1 ~v2 v3 v4
  = du_reclaim'45'alloc_6642 v3 v4
du_reclaim'45'alloc_6642 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_reclaim'45'alloc_6642 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_6656 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_reclaim'45'preserves'45'frontier_6656 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                        v7
  = du_reclaim'45'preserves'45'frontier_6656 v5 v6 v7
du_reclaim'45'preserves'45'frontier_6656 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_reclaim'45'preserves'45'frontier_6656 v0 v1 v2
  = coe
      du_stack'45'alloc'45'advances''_6680 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.stack-alloc-advances'
d_stack'45'alloc'45'advances''_6680 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
d_stack'45'alloc'45'advances''_6680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10 v11 v12
  = du_stack'45'alloc'45'advances''_6680 v10 v11 v12
du_stack'45'alloc'45'advances''_6680 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_stack'45'alloc'45'advances''_6680 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_672 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_672
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v8) (coe v0))
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_682 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_682 v7
                    v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_686 v5
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_686 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_6740 ::
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
  T_ValidAtWF_616 -> T_ValidAtWF_616
d_validityWF'45'reclaim_6740 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             ~v11 v12
  = du_validityWF'45'reclaim_6740 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v12
du_validityWF'45'reclaim_6740 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'reclaim_6740 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'frontier'45'advance_4440 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v3)))
      (coe du_reclaim'45'alloc_6642 (coe v3) (coe v8)) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v9)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v3)))
      (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_6774 ::
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
d_derive'45'mem'45'preserved'45'at_6774 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.k<start
d_k'60'start_6802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'start_6802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 v13
  = du_k'60'start_6802 v12 v13
du_k'60'start_6802 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'start_6802 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_6846 ::
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
d_derive'45'mem'45'preserved_6846 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_6880 ::
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
  T_ValidAtWF_616 -> AgdaAny -> AgdaAny -> T_ValidAtWF_616
d_validityWF'45'trace'45'preserves_6880 v0 v1 v2 ~v3 v4 v5 v6 v7
                                        ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_validityWF'45'trace'45'preserves_6880
      v0 v1 v2 v4 v5 v6 v7 v9 v11
du_validityWF'45'trace'45'preserves_6880 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  T_ValidAtWF_616 -> T_ValidAtWF_616
du_validityWF'45'trace'45'preserves_6880 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validityWF'45'mem'45'preserved_5192 (coe v0) (coe v1) (coe v2)
      (coe v4) (coe v3) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_3242 (coe v2)
            (coe v5) (coe v7) (coe v4)))
      (coe v8)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_6918 ::
  T_IRResultAWF_726 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_6918 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_6930 ::
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
d_mem'45'preserved'45'from'45'tnhw_6930 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_6962 ::
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
d_before'45'frontier'45'monotone_6962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7 v8 v9
  = du_before'45'frontier'45'monotone_6962 v7 v8 v9
du_before'45'frontier'45'monotone_6962 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_664
du_before'45'frontier'45'monotone_6962 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_672 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_672
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v6) (coe v0))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_682 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_682 v5
             v6 v7 v8
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_686 v4
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_686
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_7044 ::
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
d_mem'45'preserved'45'compose_7044 = erased
