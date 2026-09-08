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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Eval
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ClosureWellFormed._.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace'45'at'45'frontier_12 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'at'45'frontier_732
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.eval
d_eval_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_eval_24 ~v0 v1 ~v2 v3 v4 = du_eval_24 v1 v3 v4
du_eval_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_eval_24 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Eval.d_eval_12 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump
d_AllocBump_32 a0 a1 a2 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.BeforeFrontier
d_BeforeFrontier_36 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.apply-bump
d_apply'45'bump_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_40 ~v0 ~v1 ~v2 = du_apply'45'bump_40
du_apply'45'bump_40 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_40
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_936
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_82 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 -> Integer
d_next'45'heap'45'ref'45'delta_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_932
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_84 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 -> Integer
d_next'45'slot'45'delta_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_930
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.readLoc
d_readLoc_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_110 ~v0 ~v1 ~v2 = du_readLoc_110
du_readLoc_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_110
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.writeLoc
d_writeLoc_118 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_118 ~v0 v1 ~v2 = du_writeLoc_118 v1
du_writeLoc_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLoc_118 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_810 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.write-loc
d_write'45'loc_148 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'loc_148 ~v0 v1 ~v2 = du_write'45'loc_148 v1
du_write'45'loc_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_write'45'loc_148 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_write'45'loc_332
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.exec-trace
d_exec'45'trace_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_208 ~v0 v1 ~v2 = du_exec'45'trace_208 v1
du_exec'45'trace_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_208 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.TraceWF
d_TraceWF_268 a0 a1 a2 a3 a4 a5 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._._≺_
d__'8826'__444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> AgdaAny -> AgdaAny -> ()
d__'8826'__444 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.Frame
d_Frame_446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_Frame_446 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.SumTag
d_SumTag_506 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_506 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_530 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_530 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.prim-sv
d_prim'45'sv_542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_542 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_prim'45'sv_542 v4 v5
du_prim'45'sv_542 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_542 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_528
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Int_132)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_194) (coe v1)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_530
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Float_134)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_196) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlineRep
d_InlineRep_550 a0 a1 a2 a3 = ()
data T_InlineRep_550
  = C_rep'45'prim_554 MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 |
    C_rep'45'unit_556 MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.inline-sv
d_inline'45'sv_560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  T_InlineRep_550 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_560 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_inline'45'sv_560 v4 v5
du_inline'45'sv_560 ::
  T_InlineRep_550 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_560 v0 v1
  = case coe v0 of
      C_rep'45'prim_554 v2 -> coe du_prim'45'sv_542 (coe v2) (coe v1)
      C_rep'45'unit_556 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_570 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ValidAtWF_570
  = C_valid'45'unit'45'wf_760 |
    C_valid'45'pair'45'wf_786 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.IR.T_AllocMode_4
                              MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                              T_ValidAtWF_570 T_ValidAtWF_570 |
    C_valid'45'closure'45'wf_816 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                                 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                 MAlonzo.Code.Once.IR.T_AllocMode_4
                                 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                                 T_ValidAtWF_570 T_BodyCorrect_750 |
    C_valid'45'inl'45'wf_836 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                             T_ValidAtWF_570 |
    C_valid'45'inr'45'wf_856 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                             T_ValidAtWF_570 |
    C_valid'45'inl'45'reg'45'wf_874 AgdaAny T_InlineRep_550
                                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_valid'45'inr'45'reg'45'wf_892 AgdaAny T_InlineRep_550
                                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_valid'45'μ'45'wf_908 MAlonzo.Code.Once.IRTy.T_WellFormedFI_130
                           T_ValidAtWF_570 |
    C_valid'45'ν'45'wf_924 MAlonzo.Code.Once.IRTy.T_WellFormedFI_130
                           T_ValidAtWF_570 |
    C_valid'45'int'45'wf_936 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_valid'45'float'45'wf_948 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_valid'45'str'45'wf_960 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_valid'45'buffer'45'wf_972 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ValidAtWF_570
d_valid'45'primitive'45'wf_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9 v10 ~v11
  = du_valid'45'primitive'45'wf_586 v9 v10
du_valid'45'primitive'45'wf_586 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570
du_valid'45'primitive'45'wf_586 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_528
        -> coe C_valid'45'int'45'wf_936 v1
      MAlonzo.Code.Once.IRTy.C_fits'45'float_530
        -> coe C_valid'45'float'45'wf_948 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ResultPlace
d_ResultPlace_600 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ResultPlace_600
  = C_unit'45'result_990 |
    C_at'45'loc_1006 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                     T_ValidAtWF_570
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                     T_ValidAtWF_570
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_at'45'reg_1022 MAlonzo.Code.Once.IRTy.T_FitsInRegI_526
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-sv
d_place'45'sv_614 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_600 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_614 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_unit'45'result_990
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70
                (coe d_unit'45'result'45'sv'45'loc_1034 v0 v1 v2 v4 v5 v6 v8))
      C_at'45'loc_1006 v16 v17 v18 v20 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v16)
      C_at'45'reg_1022 v16 -> coe du_prim'45'sv_542 (coe v16) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-rax
d_place'45'rax_630 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_630 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase
d_IRResultBase_646 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultBase_646
  = C_constructor_1126 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
                       T_ResultPlace_600
                       MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 AgdaAny
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_656 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IRStackBudget_656
  = C_constructor_1198 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                       AgdaAny AgdaAny AgdaAny AgdaAny Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_664 a0 a1 a2 a3 a4 a5 = ()
data T_IRHeapBudget_664
  = C_constructor_1228 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_680 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultAWF_680
  = C_constructor_1330 T_IRResultBase_646 T_IRStackBudget_656
                       T_IRHeapBudget_664
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_734 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ResultPlace_600 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  T_IRStackBudget_656 -> T_IRHeapBudget_664 -> T_IRResultAWF_680
d_mk'45'IRResultAWF'45'via'45'bump_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
                                       ~v20 v21 ~v22 v23 v24 v25
  = du_mk'45'IRResultAWF'45'via'45'bump_734
      v10 v12 v13 v18 v21 v23 v24 v25
du_mk'45'IRResultAWF'45'via'45'bump_734 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  T_ResultPlace_600 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  AgdaAny ->
  T_IRStackBudget_656 -> T_IRHeapBudget_664 -> T_IRResultAWF_680
du_mk'45'IRResultAWF'45'via'45'bump_734 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1330 (coe C_constructor_1126 v0 v1 v2 v3 v4 v5)
      (coe v6) (coe v7)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_750 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_BodyCorrect_750
  = C_constructor_1430 Integer
                       (AgdaAny ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        T_ValidAtWF_570 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc
d_unit'45'result'45'sv'45'loc_1034
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub
d_rax'45'stub_1046
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_1092 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_1092 v0
  = case coe v0 of
      C_constructor_1126 v1 v2 v3 v7 v10 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace
d_trace_1094 ::
  T_IRResultBase_646 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace_1094 v0
  = case coe v0 of
      C_constructor_1126 v1 v2 v3 v7 v10 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.bump
d_bump_1096 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump_1096 v0
  = case coe v0 of
      C_constructor_1126 v1 v2 v3 v7 v10 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1098 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1098 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_1100 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1100 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_1102 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1102 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_1104 :: T_IRResultBase_646 -> T_ResultPlace_600
d_result'45'place_1104 v0
  = case coe v0 of
      C_constructor_1126 v1 v2 v3 v7 v10 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_1106 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1106 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_1110 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1110 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_1112 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230
d_trace'45'twf_1112 v0
  = case coe v0 of
      C_constructor_1126 v1 v2 v3 v7 v10 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_1118 ::
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1118 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1120 :: T_IRResultBase_646 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1120 v0
  = case coe v0 of
      C_constructor_1126 v1 v2 v3 v7 v10 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_1122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_1122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1122 v9 v10
du_final'45'alloc_1122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultBase_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_1122 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_936
      (coe d_bump_1096 (coe v1)) (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_1124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultBase_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1124 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_1164 :: T_IRStackBudget_656 -> Integer
d_max'45'slot'45'written_1164 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_1166 :: T_IRStackBudget_656 -> Integer
d_stack'45'budget_1166 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1168 ::
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1168 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1170 ::
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1170 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1172 ::
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1172 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_1178 ::
  T_IRStackBudget_656 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1178 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_1180 :: T_IRStackBudget_656 -> AgdaAny
d_trace'45'writes'45'above_1180 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1182 ::
  T_IRStackBudget_656 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1182 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_1184 :: T_IRStackBudget_656 -> AgdaAny
d_trace'45'writes'45'below_1184 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1186 ::
  T_IRStackBudget_656 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1186 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_1188 :: T_IRStackBudget_656 -> Integer
d_scratch'45'budget_1188 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_1190 ::
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1190 v0
  = case coe v0 of
      C_constructor_1198 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_1192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1192 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_slot'45'monotone_1192 v3
du_slot'45'monotone_1192 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1192 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1194 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7
  = du_slot'45'stays'45'in'45'budget_1194 v3 v4 v7
du_slot'45'stays'45'in'45'budget_1194 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  T_IRStackBudget_656 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1194 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_930
         (coe v1))
      (d_stack'45'budget_1166 (coe v2))
      (d_bump'45'fits'45'stack'45'budget_1168 (coe v2))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_1216 :: T_IRHeapBudget_664 -> Integer
d_heap'45'budget_1216 v0
  = case coe v0 of
      C_constructor_1228 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1218 ::
  T_IRHeapBudget_664 -> Integer
d_max'45'heap'45'ref'45'written_1218 v0
  = case coe v0 of
      C_constructor_1228 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1220 ::
  T_IRHeapBudget_664 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1220 v0
  = case coe v0 of
      C_constructor_1228 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1222 ::
  T_IRHeapBudget_664 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1222 v0
  = case coe v0 of
      C_constructor_1228 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1224 ::
  T_IRHeapBudget_664 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1224 v0
  = case coe v0 of
      C_constructor_1228 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_1226 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  T_IRHeapBudget_664 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1226 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_heap'45'monotone_1226 v3
du_heap'45'monotone_1226 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1226 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.base
d_base_1250 :: T_IRResultAWF_680 -> T_IRResultBase_646
d_base_1250 v0
  = case coe v0 of
      C_constructor_1330 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_1252 :: T_IRResultAWF_680 -> T_IRStackBudget_656
d_stack'45'inv_1252 v0
  = case coe v0 of
      C_constructor_1330 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_1254 :: T_IRResultAWF_680 -> T_IRHeapBudget_664
d_heap'45'inv_1254 v0
  = case coe v0 of
      C_constructor_1330 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.alloc-correct
d_alloc'45'correct_1258 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1258 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump
d_bump_1260 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_924
d_bump_1260 v0 = coe d_bump_1096 (coe d_base_1250 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-alloc
d_final'45'alloc_1262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_1262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1262 v9 v10
du_final'45'alloc_1262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_1262 v0 v1
  = coe du_final'45'alloc_1122 (coe v0) (coe d_base_1250 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-state
d_final'45'state_1264 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_1264 v0
  = coe d_final'45'state_1092 (coe d_base_1250 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frame-preserved
d_frame'45'preserved_1266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1266 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.mem-preserved-before
d_mem'45'preserved'45'before_1268 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1268 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.not-halted
d_not'45'halted_1270 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1270 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.result-place
d_result'45'place_1272 :: T_IRResultAWF_680 -> T_ResultPlace_600
d_result'45'place_1272 v0
  = coe d_result'45'place_1104 (coe d_base_1250 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace
d_trace_1274 ::
  T_IRResultAWF_680 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace_1274 v0 = coe d_trace_1094 (coe d_base_1250 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-correct
d_trace'45'correct_1276 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1276 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1278 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1278 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1280 :: T_IRResultAWF_680 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1280 v0
  = coe d_trace'45'no'45'frame'45'ops_1120 (coe d_base_1250 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-preserves-halted
d_trace'45'preserves'45'halted_1282 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1282 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-twf
d_trace'45'twf_1284 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230
d_trace'45'twf_1284 v0
  = coe d_trace'45'twf_1112 (coe d_base_1250 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1288 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1288 v0
  = coe
      d_bump'45'fits'45'stack'45'budget_1168
      (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frontier-slot-stable
d_frontier'45'slot'45'stable_1290 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1290 v0
  = coe
      d_frontier'45'slot'45'stable_1178
      (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1292 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1292 v0
  = coe
      d_max'45'slot'45'geq'45'final_1170
      (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1294 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1294 v0
  = coe
      d_max'45'slot'45'usage'45'bound_1172
      (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-written
d_max'45'slot'45'written_1296 :: T_IRResultAWF_680 -> Integer
d_max'45'slot'45'written_1296 v0
  = coe
      d_max'45'slot'45'written_1164 (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-bounded
d_scratch'45'bounded_1298 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1298 v0
  = coe d_scratch'45'bounded_1190 (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-budget
d_scratch'45'budget_1300 :: T_IRResultAWF_680 -> Integer
d_scratch'45'budget_1300 v0
  = coe d_scratch'45'budget_1188 (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-monotone
d_slot'45'monotone_1302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_1302 v9
du_slot'45'monotone_1302 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1302 v0 = coe du_slot'45'monotone_1192 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1304 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_1304 v9 v10
du_slot'45'stays'45'in'45'budget_1304 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1304 v0 v1
  = coe
      du_slot'45'stays'45'in'45'budget_1194 (coe v0)
      (coe d_bump_1096 (coe d_base_1250 (coe v1)))
      (coe d_stack'45'inv_1252 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.stack-budget
d_stack'45'budget_1306 :: T_IRResultAWF_680 -> Integer
d_stack'45'budget_1306 v0
  = coe d_stack'45'budget_1166 (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1308 ::
  T_IRResultAWF_680 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1308 v0
  = coe
      d_trace'45'slot'45'reads'45'above_1182
      (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1310 ::
  T_IRResultAWF_680 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1310 v0
  = coe
      d_trace'45'slot'45'reads'45'below_1186
      (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-above
d_trace'45'writes'45'above_1312 :: T_IRResultAWF_680 -> AgdaAny
d_trace'45'writes'45'above_1312 v0
  = coe
      d_trace'45'writes'45'above_1180 (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-below
d_trace'45'writes'45'below_1314 :: T_IRResultAWF_680 -> AgdaAny
d_trace'45'writes'45'below_1314 v0
  = coe
      d_trace'45'writes'45'below_1184 (coe d_stack'45'inv_1252 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1318 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1318 v0
  = coe
      d_bump'45'fits'45'heap'45'budget_1220
      (coe d_heap'45'inv_1254 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-budget
d_heap'45'budget_1320 :: T_IRResultAWF_680 -> Integer
d_heap'45'budget_1320 v0
  = coe d_heap'45'budget_1216 (coe d_heap'45'inv_1254 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-monotone
d_heap'45'monotone_1322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_1322 v9
du_heap'45'monotone_1322 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1322 v0 = coe du_heap'45'monotone_1226 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1324 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1324 v0
  = coe
      d_max'45'heap'45'ref'45'geq'45'final_1222
      (coe d_heap'45'inv_1254 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1326 ::
  T_IRResultAWF_680 -> Integer
d_max'45'heap'45'ref'45'written_1326 v0
  = coe
      d_max'45'heap'45'ref'45'written_1218
      (coe d_heap'45'inv_1254 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1328 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1328 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1224
      (coe d_heap'45'inv_1254 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_1410 :: T_BodyCorrect_750 -> Integer
d_body'45'capacity_1410 v0
  = case coe v0 of
      C_constructor_1430 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_1412 ::
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_1412 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.execute
d_execute_1428 ::
  T_BodyCorrect_750 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_1428 v0
  = case coe v0 of
      C_constructor_1430 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_1448 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_1448 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-via-budget
d_bound'45'via'45'budget_1460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'via'45'budget_1460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 v10 ~v11
  = du_bound'45'via'45'budget_1460 v10
du_bound'45'via'45'budget_1460 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'via'45'budget_1460 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1224
      (coe d_heap'45'inv_1254 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-alloc
d_bound'45'alloc_1464 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_680 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'alloc_1464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      ~v11
  = du_bound'45'alloc_1464 v10
du_bound'45'alloc_1464 ::
  T_IRResultAWF_680 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'alloc_1464 v0
  = coe du_bound'45'via'45'budget_1460 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_1490 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13
  = ()
data T_ClosureWellFormed_1490
  = C_constructor_1546 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.IR.T_AllocMode_4 T_ValidAtWF_570
                       T_BodyCorrect_750
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_1530 ::
  T_ClosureWellFormed_1490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1530 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_1532 ::
  T_ClosureWellFormed_1490 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1532 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_1534 ::
  T_ClosureWellFormed_1490 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_env'45'before_1534 v0
  = case coe v0 of
      C_constructor_1546 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_1536 ::
  T_ClosureWellFormed_1490 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_code'45'before_1536 v0
  = case coe v0 of
      C_constructor_1546 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_1538 ::
  T_ClosureWellFormed_1490 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_1538 v0
  = case coe v0 of
      C_constructor_1546 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_1540 ::
  T_ClosureWellFormed_1490 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1540 v0
  = case coe v0 of
      C_constructor_1546 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_1542 :: T_ClosureWellFormed_1490 -> T_ValidAtWF_570
d_env'45'valid_1542 v0
  = case coe v0 of
      C_constructor_1546 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_1544 ::
  T_ClosureWellFormed_1490 -> T_BodyCorrect_750
d_body'45'correct_1544 v0
  = case coe v0 of
      C_constructor_1546 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_1560 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ClosureValidWF_1560
  = C_constructor_1634 MAlonzo.Code.Once.IRTy.T_IRTy_6
                       MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ValidAtWF_570 T_BodyCorrect_750
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_1604 ::
  T_ClosureValidWF_1560 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1604 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body
d_body_1606 ::
  T_ClosureValidWF_1560 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1606 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env
d_env_1608 :: T_ClosureValidWF_1560 -> AgdaAny
d_env_1608 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body<bound
d_body'60'bound_1610 ::
  T_ClosureValidWF_1560 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_1610 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-loc
d_env'45'loc_1612 ::
  T_ClosureValidWF_1560 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_1612 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_1614 ::
  T_ClosureValidWF_1560 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_1614 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.mEnv
d_mEnv_1616 ::
  T_ClosureValidWF_1560 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1616 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-ptr
d_env'45'ptr_1618 ::
  T_ClosureValidWF_1560 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1618 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_1620 ::
  T_ClosureValidWF_1560 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1620 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-before
d_env'45'before_1622 ::
  T_ClosureValidWF_1560 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_env'45'before_1622 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1624 ::
  T_ClosureValidWF_1560 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_1624 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-valid
d_env'45'valid_1626 :: T_ClosureValidWF_1560 -> T_ValidAtWF_570
d_env'45'valid_1626 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-correct
d_body'45'correct_1628 ::
  T_ClosureValidWF_1560 -> T_BodyCorrect_750
d_body'45'correct_1628 v0
  = case coe v0 of
      C_constructor_1634 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1632 ::
  T_ClosureValidWF_1560 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1632 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_1650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_ClosureValidWF_1560
d_decomposeClosureWF_1650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10
  = du_decomposeClosureWF_1650 v10
du_decomposeClosureWF_1650 ::
  T_ValidAtWF_570 -> T_ClosureValidWF_1560
du_decomposeClosureWF_1650 v0
  = case coe v0 of
      C_valid'45'closure'45'wf_816 v2 v5 v6 v8 v10 v12 v13 v14 v17 v18 v19 v20
        -> coe C_constructor_1634 v2 v5 v6 v8 v10 v13 v12 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.Place
d_Place_1680 a0 a1 a2 = ()
data T_Place_1680
  = C_AtStorage_1682 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_InReg_1684 MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InputPlace
d_InputPlace_1696 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InputPlace_1696
  = C_in'45'at'45'loc_1710 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           T_ValidAtWF_570
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_in'45'at'45'reg_1714 MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 |
    C_in'45'unit_1716
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.input-sv
d_input'45'sv_1728 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_InputPlace_1696 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_input'45'sv_1728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_input'45'sv_1728 v6 v7 v8
du_input'45'sv_1728 ::
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_InputPlace_1696 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_input'45'sv_1728 v0 v1 v2
  = case coe v2 of
      C_in'45'at'45'loc_1710 v3 v4 v5
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3)
      C_in'45'at'45'reg_1714 v3
        -> coe du_prim'45'sv_542 (coe v3) (coe v0)
      C_in'45'unit_1716
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v1))
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.input-read
d_input'45'read_1750 ::
  T_InputPlace_1696 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_input'45'read_1750 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_1756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> Integer -> ()
d_RecDispatcherWF_1756 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF
d_PairValidWF_1790 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_PairValidWF_1790
  = C_constructor_1848 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ValidAtWF_570 T_ValidAtWF_570
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-loc
d_fst'45'loc_1826 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_1826 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-loc
d_snd'45'loc_1828 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_1828 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mA
d_mA_1830 ::
  T_PairValidWF_1790 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1830 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mB
d_mB_1832 ::
  T_PairValidWF_1790 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1832 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-ptr
d_fst'45'ptr_1834 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_1834 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-ptr
d_snd'45'ptr_1836 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_1836 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-before
d_fst'45'before_1838 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_fst'45'before_1838 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-before
d_snd'45'before_1840 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_snd'45'before_1840 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_1842 ::
  T_PairValidWF_1790 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_1842 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-valid
d_fst'45'valid_1844 :: T_PairValidWF_1790 -> T_ValidAtWF_570
d_fst'45'valid_1844 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-valid
d_snd'45'valid_1846 :: T_PairValidWF_1790 -> T_ValidAtWF_570
d_snd'45'valid_1846 v0
  = case coe v0 of
      C_constructor_1848 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_1864 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_PairValidWF_1790
d_decomposePairWF_1864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_decomposePairWF_1864 v10
du_decomposePairWF_1864 :: T_ValidAtWF_570 -> T_PairValidWF_1790
du_decomposePairWF_1864 v0
  = case coe v0 of
      C_valid'45'pair'45'wf_786 v8 v9 v11 v12 v13 v16 v17 v18 v19 v20
        -> coe C_constructor_1848 v8 v9 v11 v12 v16 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PayloadAt
d_PayloadAt_1900 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_PayloadAt_1900
  = C_payload'45'at'45'loc_1916 MAlonzo.Code.Once.IR.T_AllocMode_4
                                MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                                T_ValidAtWF_570 |
    C_payload'45'in'45'reg_1920 T_InlineRep_550
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.payload-sv
d_payload'45'sv_1932 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_PayloadAt_1900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_payload'45'sv_1932 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_payload'45'sv_1932 v5 v8
du_payload'45'sv_1932 ::
  AgdaAny ->
  T_PayloadAt_1900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_payload'45'sv_1932 v0 v1
  = case coe v1 of
      C_payload'45'at'45'loc_1916 v2 v3 v5 v6
        -> coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3)
      C_payload'45'in'45'reg_1920 v2
        -> coe du_inline'45'sv_560 (coe v2) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.payload-read
d_payload'45'read_1952 ::
  T_PayloadAt_1900 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'read_1952 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF
d_InlValidWF_1970 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InlValidWF_1970
  = C_constructor_2000 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_PayloadAt_1900
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.a
d_a_1992 :: T_InlValidWF_1970 -> AgdaAny
d_a_1992 v0
  = case coe v0 of
      C_constructor_2000 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_1994 ::
  T_InlValidWF_1970 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_1994 v0
  = case coe v0 of
      C_constructor_2000 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload
d_payload_1996 :: T_InlValidWF_1970 -> T_PayloadAt_1900
d_payload_1996 v0
  = case coe v0 of
      C_constructor_2000 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_1998 ::
  T_InlValidWF_1970 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_1998 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF
d_InrValidWF_2014 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InrValidWF_2014
  = C_constructor_2044 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_PayloadAt_1900
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.b
d_b_2036 :: T_InrValidWF_2014 -> AgdaAny
d_b_2036 v0
  = case coe v0 of
      C_constructor_2044 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_2038 ::
  T_InrValidWF_2014 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sucLoc'45'before_2038 v0
  = case coe v0 of
      C_constructor_2044 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload
d_payload_2040 :: T_InrValidWF_2014 -> T_PayloadAt_1900
d_payload_2040 v0
  = case coe v0 of
      C_constructor_2044 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_2042 ::
  T_InrValidWF_2014 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_2042 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_2060 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_InlValidWF_1970
d_decomposeInlWF_2060 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInlWF_2060 v7 v10
du_decomposeInlWF_2060 ::
  AgdaAny -> T_ValidAtWF_570 -> T_InlValidWF_1970
du_decomposeInlWF_2060 v0 v1
  = case coe v1 of
      C_valid'45'inl'45'wf_836 v8 v10 v11 v14 v15 v16
        -> coe
             C_constructor_2000 v0 v15
             (coe C_payload'45'at'45'loc_1916 v10 v8 v14 v16)
      C_valid'45'inl'45'reg'45'wf_874 v9 v11 v13
        -> coe
             C_constructor_2000 v0 v13 (coe C_payload'45'in'45'reg_1920 v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_2102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_InrValidWF_2014
d_decomposeInrWF_2102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInrWF_2102 v7 v10
du_decomposeInrWF_2102 ::
  AgdaAny -> T_ValidAtWF_570 -> T_InrValidWF_2014
du_decomposeInrWF_2102 v0 v1
  = case coe v1 of
      C_valid'45'inr'45'wf_856 v8 v10 v11 v14 v15 v16
        -> coe
             C_constructor_2044 v0 v15
             (coe C_payload'45'at'45'loc_1916 v10 v8 v14 v16)
      C_valid'45'inr'45'reg'45'wf_892 v9 v11 v13
        -> coe
             C_constructor_2044 v0 v13 (coe C_payload'45'in'45'reg_1920 v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_2138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570
d_valid'45'to'45'validWF'45'unit_2138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_valid'45'to'45'validWF'45'unit_2138
du_valid'45'to'45'validWF'45'unit_2138 :: T_ValidAtWF_570
du_valid'45'to'45'validWF'45'unit_2138
  = coe C_valid'45'unit'45'wf_760
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_2154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'mem'45'only_2154 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9
                                 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'only_2154 v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'only_2154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'mem'45'only_2154 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_760))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2220 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v31))
                           (coe
                              du_sv''_2222 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2376 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2420 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
               -> coe C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
             C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
               -> coe C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2272 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_908 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_908 v15
                    (coe
                       du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_924 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_924 v15
                    (coe
                       du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_936 v14 -> coe C_valid'45'int'45'wf_936 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_948 v14
               -> coe C_valid'45'float'45'wf_948 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_960 v14 -> coe C_valid'45'str'45'wf_960 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_972 v14
               -> coe C_valid'45'buffer'45'wf_972 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2216 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2218 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_2220 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_fv''_2220 v0 v1 v2 v4 v5 v7 v10 v11 v14 v16 v24
du_fv''_2220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_2220 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_2222 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_sv''_2222 v0 v1 v2 v4 v6 v8 v10 v11 v15 v17 v25
du_sv''_2222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_2222 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2268 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2268 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2270 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2270 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_2272 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            v14 ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_ev''_2272 v0 v1 v2 v4 v8 v9 v12 v14 v16 v17 v24
du_ev''_2272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_2272 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_2372 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2374 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_2376 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2376 v0 v1 v2 v4 v5 v8 v9 v12 v13 v14 v20
du_pv''_2376 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_2376 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2416 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_2416 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2418 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2418 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_2420 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2420 v0 v1 v2 v4 v6 v8 v9 v12 v13 v14 v20
du_pv''_2420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_2420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2154 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_2548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'write'45'at'45'frontier_2548 v0 v1 v2 ~v3 v4 v5 v6
                                             ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'frontier_2548
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'frontier_2548 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'write'45'at'45'frontier_2548 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_760)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2610 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_2612 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2800 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
               -> coe C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
             C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
               -> coe C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2660 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_908 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_908 v15
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_924 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_924 v15
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_936 v14 -> coe C_valid'45'int'45'wf_936 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_948 v14
               -> coe C_valid'45'float'45'wf_948 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_960 v14 -> coe C_valid'45'str'45'wf_960 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_972 v14
               -> coe C_valid'45'buffer'45'wf_972 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2606 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2606 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2608 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2608 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_2610 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2610 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_2610 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_2610 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_2612 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_2612 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_2612 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_2612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2656 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2656 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2658 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2658 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_2660 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_2660 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_2660 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_2660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_2754 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2756 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_2758 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2758 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_2758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_2758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_2796 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2798 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_2800 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2800 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_2800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_2800 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2548 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_2916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'write'45'at'45'suc'45'frontier_2916 v0 v1 v2 ~v3 v4
                                                    v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'suc'45'frontier_2916
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'suc'45'frontier_2916 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'write'45'at'45'suc'45'frontier_2916 v0 v1 v2 v3 v4
                                                     v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_760)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2978 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_2980 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_3126 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_3168 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
               -> coe C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
             C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
               -> coe C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_3028 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_908 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_908 v15
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_924 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_924 v15
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_936 v14 -> coe C_valid'45'int'45'wf_936 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_948 v14
               -> coe C_valid'45'float'45'wf_948 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_960 v14 -> coe C_valid'45'str'45'wf_960 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_972 v14
               -> coe C_valid'45'buffer'45'wf_972 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2974 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2976 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_2978 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2978 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_2978 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_2978 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_2980 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_2980 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_2980 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_2980 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_3024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_3024 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_3026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_3026 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_3028 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_3028 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_3028 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_3028 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3122 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_3122 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3124 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3124 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_3126 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3126 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_3126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_3126 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_3164 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3166 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_3168 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3168 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_3168 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_3168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2916 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-sv-at-frontier
d_validityWF'45'write'45'sv'45'at'45'frontier_3284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'write'45'sv'45'at'45'frontier_3284 v0 v1 v2 ~v3 v4
                                                   v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'sv'45'at'45'frontier_3284
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'sv'45'at'45'frontier_3284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'write'45'sv'45'at'45'frontier_3284 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_760)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_3346 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_3348 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_3494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_3536 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
               -> coe C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
             C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
               -> coe C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_3396 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_908 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_908 v15
                    (coe
                       du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_924 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_924 v15
                    (coe
                       du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_936 v14 -> coe C_valid'45'int'45'wf_936 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_948 v14
               -> coe C_valid'45'float'45'wf_948 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_960 v14 -> coe C_valid'45'str'45'wf_960 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_972 v14
               -> coe C_valid'45'buffer'45'wf_972 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_3342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_3342 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_3344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_3344 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_3346 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_3346 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_3346 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_3346 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_3348 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_3348 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_3348 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_3348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_3392 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_3392 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_3394 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_3394 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_3396 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_3396 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_3396 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_3396 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_3490 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3492 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_3494 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3494 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_3494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_3494 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_3532 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3534 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_3536 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3536 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_3536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_3536 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'frontier_3284 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-sv-at-suc-frontier
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 v0 v1 v2
                                                          ~v3 v4 v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 v0 v1 v2
                                                           v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_760)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_3714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_3716 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_3862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_3904 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
               -> coe C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
             C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
               -> coe C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_3764 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_908 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_908 v15
                    (coe
                       du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_924 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_924 v15
                    (coe
                       du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_936 v14 -> coe C_valid'45'int'45'wf_936 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_948 v14
               -> coe C_valid'45'float'45'wf_948 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_960 v14 -> coe C_valid'45'str'45'wf_960 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_972 v14
               -> coe C_valid'45'buffer'45'wf_972 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_3710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_3710 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_3712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_3712 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_3714 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_3714 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_3714 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_3714 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_3716 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_3716 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_3716 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_3716 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_3760 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_3760 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_3762 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_3762 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_3764 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_3764 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_3764 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_3764 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3858 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_3858 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3860 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_3862 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3862 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_3862 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_3862 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_3900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_3900 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_3902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_3902 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_3904 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_3904 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_3904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_3904 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'sv'45'at'45'suc'45'frontier_3652 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_4022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'alloc'45'advance_4022 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
                                      v9 v10
  = du_validityWF'45'alloc'45'advance_4022
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10
du_validityWF'45'alloc'45'advance_4022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer -> T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'alloc'45'advance_4022 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v9) (coe C_valid'45'unit'45'wf_760))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> case coe v9 of
                    C_valid'45'pair'45'wf_786 v21 v22 v24 v25 v26 v29 v30 v31 v32 v33
                      -> coe
                           C_valid'45'pair'45'wf_786 v21 v22 v24 v25 v26
                           (coe du_fb''_4076 (coe v3) (coe v21) (coe v29))
                           (coe du_sb''_4078 (coe v3) (coe v22) (coe v30))
                           (coe du_slb''_4080 (coe v3) (coe v6) (coe v31))
                           (coe
                              du_fv''_4082 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v7) (coe v8) (coe v21) (coe v24) (coe v32))
                           (coe
                              du_sv''_4084 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                              (coe v13) (coe v7) (coe v8) (coe v22) (coe v25) (coe v33))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
        -> case coe v9 of
             C_valid'45'inl'45'wf_836 v18 v20 v21 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v27
                      -> coe
                           C_valid'45'inl'45'wf_836 v18 v20 v21
                           (coe du_pb''_4218 (coe v3) (coe v18) (coe v24))
                           (coe du_slb''_4220 (coe v3) (coe v6) (coe v25))
                           (coe
                              du_pv''_4222 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v7)
                              (coe v8) (coe v27) (coe v18) (coe v20) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v18 v20 v21 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v27
                      -> coe
                           C_valid'45'inr'45'wf_856 v18 v20 v21
                           (coe du_pb''_4258 (coe v3) (coe v18) (coe v24))
                           (coe du_slb''_4260 (coe v3) (coe v6) (coe v25))
                           (coe
                              du_pv''_4262 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v7)
                              (coe v8) (coe v27) (coe v18) (coe v20) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v19 v21 v23
               -> coe
                    C_valid'45'inl'45'reg'45'wf_874 v19 v21
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
                       (coe v3)
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                       (coe v23))
             C_valid'45'inr'45'reg'45'wf_892 v19 v21 v23
               -> coe
                    C_valid'45'inr'45'reg'45'wf_892 v19 v21
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
                       (coe v3)
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v6))
                       (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
        -> case coe v9 of
             C_valid'45'closure'45'wf_816 v13 v16 v17 v19 v21 v23 v24 v25 v28 v29 v30 v31
               -> coe
                    C_valid'45'closure'45'wf_816 v13 v16 v17 v19 v21 v23 v24 v25
                    (coe du_eb''_4126 (coe v3) (coe v21) (coe v28))
                    (coe du_slb''_4128 (coe v3) (coe v6) (coe v29))
                    (coe
                       du_ev''_4130 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                       (coe v13) (coe v17) (coe v21) (coe v23) (coe v30))
                    v31
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
        -> case coe v9 of
             C_valid'45'μ'45'wf_908 v16 v18
               -> coe
                    C_valid'45'μ'45'wf_908 v16
                    (coe
                       du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v16) v5)
                       (coe v6) (coe v7) (coe v8) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
        -> case coe v9 of
             C_valid'45'ν'45'wf_924 v16 v18
               -> coe
                    C_valid'45'ν'45'wf_924 v16
                    (coe
                       du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v16) v5)
                       (coe v6) (coe v7) (coe v8) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v9 of
             C_valid'45'int'45'wf_936 v15
               -> coe
                    C_valid'45'int'45'wf_936
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v9 of
             C_valid'45'float'45'wf_948 v15
               -> coe
                    C_valid'45'float'45'wf_948
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v9 of
             C_valid'45'str'45'wf_960 v15
               -> coe
                    C_valid'45'str'45'wf_960
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v9 of
             C_valid'45'buffer'45'wf_972 v15
               -> coe
                    C_valid'45'buffer'45'wf_972
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_4076 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_fb''_4076 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23
  = du_fb''_4076 v4 v12 v19
du_fb''_4076 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_fb''_4076 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_4078 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sb''_4078 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_sb''_4078 v4 v13 v20
du_sb''_4078 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_sb''_4078 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4080 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4080 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_slb''_4080 v4 v9 v21
du_slb''_4080 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4080 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_4082 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_fv''_4082 v0 v1 v2 v4 v5 v7 v10 v11 v12 v14 v22
du_fv''_4082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_4082 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v8) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_4084 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_sv''_4084 v0 v1 v2 v4 v6 v8 v10 v11 v13 v15 v23
du_sv''_4084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_4084 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v8) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_4126 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_eb''_4126 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_eb''_4126 v4 v14 v20
du_eb''_4126 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_eb''_4126 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4128 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_slb''_4128 v4 v7 v21
du_slb''_4128 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4128 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_4130 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_ev''_4130 v0 v1 v2 v4 v8 v9 v10 v12 v14 v15 v22
du_ev''_4130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_4130 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v8) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4218 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_pb''_4218 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_4218 v4 v11 v16
du_pb''_4218 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_pb''_4218 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4220 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4220 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_4220 v4 v7 v17
du_slb''_4220 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4220 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_4222 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_4222 v0 v1 v2 v4 v5 v8 v9 v10 v11 v12 v18
du_pv''_4222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_4222 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v8) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4258 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_pb''_4258 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_4258 v4 v11 v16
du_pb''_4258 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_pb''_4258 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4260 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4260 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_4260 v4 v7 v17
du_slb''_4260 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4260 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_792
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_4262 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_4262 v0 v1 v2 v4 v6 v8 v9 v10 v11 v12 v18
du_pv''_4262 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_4262 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_4022 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v8) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_4366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'frontier'45'advance_4366 v0 v1 v2 ~v3 v4 v5 v6 v7
                                         v8 v9 ~v10 v11 v12 v13
  = du_validityWF'45'frontier'45'advance_4366
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_validityWF'45'frontier'45'advance_4366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'frontier'45'advance_4366 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 v11
  = case coe v5 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v6) (coe seq (coe v11) (coe C_valid'45'unit'45'wf_760))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
               -> case coe v11 of
                    C_valid'45'pair'45'wf_786 v23 v24 v26 v27 v28 v31 v32 v33 v34 v35
                      -> coe
                           C_valid'45'pair'45'wf_786 v23 v24 v26 v27 v28
                           (coe du_fb''_4432 (coe v9) (coe v10) (coe v23) (coe v31))
                           (coe du_sb''_4434 (coe v9) (coe v10) (coe v24) (coe v32))
                           (coe du_slb''_4436 (coe v7) (coe v9) (coe v10) (coe v33))
                           (coe
                              du_fv''_4438 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                              (coe v14) (coe v8) (coe v9) (coe v10) (coe v23) (coe v26)
                              (coe v34))
                           (coe
                              du_sv''_4440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
                              (coe v15) (coe v8) (coe v9) (coe v10) (coe v24) (coe v27)
                              (coe v35))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
        -> case coe v11 of
             C_valid'45'inl'45'wf_836 v20 v22 v23 v26 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                      -> coe
                           C_valid'45'inl'45'wf_836 v20 v22 v23
                           (coe du_pb''_4598 (coe v9) (coe v10) (coe v20) (coe v26))
                           (coe du_slb''_4600 (coe v7) (coe v9) (coe v10) (coe v27))
                           (coe
                              du_pv''_4602 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                              (coe v8) (coe v9) (coe v10) (coe v29) (coe v20) (coe v22)
                              (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v20 v22 v23 v26 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                      -> coe
                           C_valid'45'inr'45'wf_856 v20 v22 v23
                           (coe du_pb''_4644 (coe v9) (coe v10) (coe v20) (coe v26))
                           (coe du_slb''_4646 (coe v7) (coe v9) (coe v10) (coe v27))
                           (coe
                              du_pv''_4648 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
                              (coe v8) (coe v9) (coe v10) (coe v29) (coe v20) (coe v22)
                              (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v21 v23 v25
               -> coe
                    C_valid'45'inl'45'reg'45'wf_874 v21 v23
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                       (coe v9) (coe v10)
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                       (coe v25))
             C_valid'45'inr'45'reg'45'wf_892 v21 v23 v25
               -> coe
                    C_valid'45'inr'45'reg'45'wf_892 v21 v23
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                       (coe v9) (coe v10)
                       (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v7))
                       (coe v25))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v12 v13
        -> case coe v11 of
             C_valid'45'closure'45'wf_816 v15 v18 v19 v21 v23 v25 v26 v27 v30 v31 v32 v33
               -> coe
                    C_valid'45'closure'45'wf_816 v15 v18 v19 v21 v23 v25 v26 v27
                    (coe du_eb''_4488 (coe v9) (coe v10) (coe v23) (coe v30))
                    (coe du_slb''_4490 (coe v7) (coe v9) (coe v10) (coe v31))
                    (coe
                       du_ev''_4492 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                       (coe v9) (coe v10) (coe v15) (coe v19) (coe v23) (coe v25)
                       (coe v32))
                    v33
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
        -> case coe v11 of
             C_valid'45'μ'45'wf_908 v18 v20
               -> coe
                    C_valid'45'μ'45'wf_908 v18
                    (coe
                       du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v5))
                       (coe
                          du_eval_24 v1 v5
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v5))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v18) v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
        -> case coe v11 of
             C_valid'45'ν'45'wf_924 v18 v20
               -> coe
                    C_valid'45'ν'45'wf_924 v18
                    (coe
                       du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v5))
                       (coe
                          du_eval_24 v1 v5
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v5))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v18) v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v11 of
             C_valid'45'int'45'wf_936 v17
               -> coe
                    C_valid'45'int'45'wf_936
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v11 of
             C_valid'45'float'45'wf_948 v17
               -> coe
                    C_valid'45'float'45'wf_948
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v11 of
             C_valid'45'str'45'wf_960 v17
               -> coe
                    C_valid'45'str'45'wf_960
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v11 of
             C_valid'45'buffer'45'wf_972 v17
               -> coe
                    C_valid'45'buffer'45'wf_972
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_4432 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_fb''_4432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_fb''_4432 v13 v14 v15 v22
du_fb''_4432 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_fb''_4432 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_4434 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_sb''_4434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25 ~v26
  = du_sb''_4434 v13 v14 v16 v23
du_sb''_4434 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_sb''_4434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4436 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25 ~v26
  = du_slb''_4436 v10 v13 v14 v24
du_slb''_4436 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4436 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_4438 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 ~v9 ~v10 v11 ~v12 v13 v14
            v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
  = du_fv''_4438 v0 v1 v2 v4 v5 v6 v8 v11 v13 v14 v15 v17 v25
du_fv''_4438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_4438 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10) (coe v7)
      (coe v8) (coe v9) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_4440 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 ~v12 v13 v14
            ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
  = du_sv''_4440 v0 v1 v2 v4 v5 v7 v9 v11 v13 v14 v16 v18 v26
du_sv''_4440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_4440 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10) (coe v7)
      (coe v8) (coe v9) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_4488 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_eb''_4488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25 ~v26
  = du_eb''_4488 v11 v12 v17 v23
du_eb''_4488 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_eb''_4488 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
             ~v26
  = du_slb''_4490 v8 v11 v12 v24
du_slb''_4490 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4490 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_4492 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
  = du_ev''_4492 v0 v1 v2 v4 v5 v9 v11 v12 v13 v15 v17 v18 v25
du_ev''_4492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_4492 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v10) (coe v5)
      (coe v6) (coe v7) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_pb''_4598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_4598 v11 v12 v14 v19
du_pb''_4598 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_pb''_4598 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4600 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_4600 v8 v11 v12 v20
du_slb''_4600 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4600 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_4602 v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_4602 v0 v1 v2 v4 v5 v6 v9 v11 v12 v13 v14 v15 v21
du_pv''_4602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_4602 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v10) (coe v6)
      (coe v7) (coe v8) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_4644 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_pb''_4644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_4644 v11 v12 v14 v19
du_pb''_4644 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_pb''_4644 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_4646 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_slb''_4646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_4646 v8 v11 v12 v20
du_slb''_4646 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_slb''_4646 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_4648 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_4648 v0 v1 v2 v4 v5 v7 v9 v11 v12 v13 v14 v15 v21
du_pv''_4648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_4648 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v10) (coe v6)
      (coe v7) (coe v8) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_4792 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'with'45'bf'45'transfer_4792 ~v0 v1 ~v2 ~v3 v4 v5 v6
                                            ~v7 ~v8 ~v9 v10 v11
  = du_validityWF'45'with'45'bf'45'transfer_4792 v1 v4 v5 v6 v10 v11
du_validityWF'45'with'45'bf'45'transfer_4792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658) ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'with'45'bf'45'transfer_4792 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v2) (coe seq (coe v5) (coe C_valid'45'unit'45'wf_760))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v5 of
                    C_valid'45'pair'45'wf_786 v17 v18 v20 v21 v22 v25 v26 v27 v28 v29
                      -> coe
                           C_valid'45'pair'45'wf_786 v17 v18 v20 v21 v22 (coe v4 v17 v25)
                           (coe v4 v18 v26)
                           (coe
                              v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                              v27)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0) (coe v6)
                              (coe v8) (coe v17) (coe v4) (coe v28))
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0) (coe v7)
                              (coe v9) (coe v18) (coe v4) (coe v29))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v6 v7
        -> case coe v5 of
             C_valid'45'inl'45'wf_836 v14 v16 v17 v20 v21 v22
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v23
                      -> coe
                           C_valid'45'inl'45'wf_836 v14 v16 v17 (coe v4 v14 v20)
                           (coe
                              v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                              v21)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0) (coe v6)
                              (coe v23) (coe v14) (coe v4) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v14 v16 v17 v20 v21 v22
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v23
                      -> coe
                           C_valid'45'inr'45'wf_856 v14 v16 v17 (coe v4 v14 v20)
                           (coe
                              v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                              v21)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0) (coe v7)
                              (coe v23) (coe v14) (coe v4) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v15 v17 v19
               -> coe
                    C_valid'45'inl'45'reg'45'wf_874 v15 v17
                    (coe
                       v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                       v19)
             C_valid'45'inr'45'reg'45'wf_892 v15 v17 v19
               -> coe
                    C_valid'45'inr'45'reg'45'wf_892 v15 v17
                    (coe
                       v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                       v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v6 v7
        -> case coe v5 of
             C_valid'45'closure'45'wf_816 v9 v12 v13 v15 v17 v19 v20 v21 v24 v25 v26 v27
               -> coe
                    C_valid'45'closure'45'wf_816 v9 v12 v13 v15 v17 v19 v20 v21
                    (coe v4 v17 v24)
                    (coe
                       v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                       v25)
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0) (coe v9)
                       (coe v13) (coe v17) (coe v4) (coe v26))
                    v27
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v6
        -> case coe v5 of
             C_valid'45'μ'45'wf_908 v12 v14
               -> coe
                    C_valid'45'μ'45'wf_908 v12
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v6) (coe v1))
                       (coe
                          du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v6) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v12) v2)
                       (coe v3) (coe v4) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v6
        -> case coe v5 of
             C_valid'45'ν'45'wf_924 v12 v14
               -> coe
                    C_valid'45'ν'45'wf_924 v12
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_4792 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v6) (coe v1))
                       (coe
                          du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v6) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v12) v2)
                       (coe v3) (coe v4) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v5 of
             C_valid'45'int'45'wf_936 v11
               -> coe C_valid'45'int'45'wf_936 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v5 of
             C_valid'45'float'45'wf_948 v11
               -> coe C_valid'45'float'45'wf_948 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v5 of
             C_valid'45'str'45'wf_960 v11
               -> coe C_valid'45'str'45'wf_960 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v5 of
             C_valid'45'buffer'45'wf_972 v11
               -> coe C_valid'45'buffer'45'wf_972 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_5120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'mem'45'preserved_5120 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8
                                      v9 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'preserved_5120
      v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'preserved_5120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'mem'45'preserved_5120 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_760))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_786 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_5186 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_5188 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_836 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_5342 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_5386 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
               -> coe C_valid'45'inl'45'reg'45'wf_874 v18 v20 v22
             C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
               -> coe C_valid'45'inr'45'reg'45'wf_892 v18 v20 v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_816 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_5238 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_908 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_908 v15
                    (coe
                       du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_924 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_924 v15
                    (coe
                       du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_936 v14 -> coe C_valid'45'int'45'wf_936 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_948 v14
               -> coe C_valid'45'float'45'wf_948 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_960 v14 -> coe C_valid'45'str'45'wf_960 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_972 v14
               -> coe C_valid'45'buffer'45'wf_972 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_5182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_5182 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_5184 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_5184 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_5186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_fv''_5186 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24 ~v25
  = du_fv''_5186 v0 v1 v2 v4 v5 v7 v10 v11 v14 v16 v21 v24
du_fv''_5186 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_fv''_5186 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_5188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570 -> T_ValidAtWF_570
d_sv''_5188 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 v25
  = du_sv''_5188 v0 v1 v2 v4 v6 v8 v10 v11 v15 v17 v22 v25
du_sv''_5188 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_sv''_5188 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_5234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_5234 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_5236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_5236 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_5238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_BodyCorrect_750 -> T_ValidAtWF_570
d_ev''_5238 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            v14 ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 v24 ~v25
  = du_ev''_5238 v0 v1 v2 v4 v8 v9 v12 v14 v16 v17 v22 v24
du_ev''_5238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_ev''_5238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_5338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_5338 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_5340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_5340 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_5342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_5342 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_5342 v0 v1 v2 v4 v5 v8 v9 v12 v13 v14 v18 v20
du_pv''_5342 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_5342 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_5382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny
d_tg''_5382 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_5384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_5384 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_5386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_pv''_5386 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_5386 v0 v1 v2 v4 v6 v8 v9 v12 v13 v14 v18 v20
du_pv''_5386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_pv''_5386 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.inputPlace-transport
d_inputPlace'45'transport_5518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_InputPlace_1696 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InputPlace_1696
d_inputPlace'45'transport_5518 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10
                               ~v11 v12 v13 ~v14 ~v15
  = du_inputPlace'45'transport_5518
      v0 v1 v2 v3 v5 v6 v7 v8 v9 v10 v12 v13
du_inputPlace'45'transport_5518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_InputPlace_1696 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_InputPlace_1696
du_inputPlace'45'transport_5518 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11
  = case coe v9 of
      C_in'45'at'45'loc_1710 v12 v13 v14
        -> coe
             C_in'45'at'45'loc_1710 v12
             (coe
                du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
                (coe v2) (coe v4) (coe v5) (coe v3) (coe v6) (coe v12) (coe v8)
                (coe v10) (coe v11)
                (coe
                   du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
                   (coe v4) (coe v3) (coe v6) (coe v7) (coe v8) (coe v13)))
             (coe
                MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_862
                (coe v10) (coe v11) (coe v12) (coe v14))
      C_in'45'at'45'reg_1714 v12 -> coe C_in'45'at'45'reg_1714 v12
      C_in'45'unit_1716 -> coe C_in'45'unit_1716
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_5572 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'mem'45'preserved'45'excluding_5572 ~v0 ~v1 ~v2 ~v3
                                                   ~v4
  = du_validityWF'45'mem'45'preserved'45'excluding_5572
du_validityWF'45'mem'45'preserved'45'excluding_5572 ::
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'mem'45'preserved'45'excluding_5572
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocInRegions
d_LocInRegions_5580 a0 a1 a2 a3 a4 a5 a6 = ()
data T_LocInRegions_5580
  = C_loc'45'in'45'input_5590 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'fresh_5594 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'anc_5600 AgdaAny | C_loc'45'in'45'heap_5604
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_5622 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> Integer -> T_ValidAtWF_570 -> ()
d_LocsInRegions_5622 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_5812 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_LocInRegions_5580 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_5812 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_5884
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\956-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_5906
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\957-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938 v0
                                                                 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18
                                                                 v19 v20
  = du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v19 v20
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                  v12 v13 v14 v15
  = case coe v14 of
      C_valid'45'unit'45'wf_760 -> coe C_valid'45'unit'45'wf_760
      C_valid'45'pair'45'wf_786 v23 v24 v26 v27 v28 v31 v32 v33 v34 v35
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v36 v37
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                             -> case coe v41 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                    -> case coe v43 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                           -> coe
                                                C_valid'45'pair'45'wf_786 v23 v24 v26 v27 v28 v31
                                                v32 v33
                                                (coe
                                                   du_fv''_6024 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v36) (coe v38) (coe v23) (coe v26)
                                                   (coe v31) (coe v34) (coe v44))
                                                (coe
                                                   du_sv''_6026 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v37) (coe v39) (coe v24) (coe v27)
                                                   (coe v32) (coe v35) (coe v45))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_816 v17 v20 v21 v23 v25 v27 v28 v29 v32 v33 v34 v35
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
               -> case coe v37 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                      -> coe
                           C_valid'45'closure'45'wf_816 v17 v20 v21 v23 v25 v27 v28 v29 v32
                           v33
                           (coe
                              du_ev''_6098 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8) (coe v9)
                              (coe v10) (coe v11) (coe v12) (coe v13) (coe v17) (coe v21)
                              (coe v25) (coe v27) (coe v32) (coe v34) (coe v39))
                           v35
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'wf_836 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inl'45'wf_836 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_6242 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v31) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_856 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inr'45'wf_856 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_6302 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v32) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'reg'45'wf_874 v23 v25 v27
        -> coe
             seq (coe v15) (coe C_valid'45'inl'45'reg'45'wf_874 v23 v25 v27)
      C_valid'45'inr'45'reg'45'wf_892 v23 v25 v27
        -> coe
             seq (coe v15) (coe C_valid'45'inr'45'reg'45'wf_892 v23 v25 v27)
      C_valid'45'μ'45'wf_908 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v24
               -> coe
                    C_valid'45'μ'45'wf_908 v21
                    (coe
                       d_μ'45'validity'45'in'45'regions'45'stub_5884 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'ν'45'wf_924 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v24
               -> coe
                    C_valid'45'ν'45'wf_924 v21
                    (coe
                       d_ν'45'validity'45'in'45'regions'45'stub_5906 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_936 v21 -> coe C_valid'45'int'45'wf_936 v21
      C_valid'45'float'45'wf_948 v21
        -> coe C_valid'45'float'45'wf_948 v21
      C_valid'45'str'45'wf_960 v21 -> coe C_valid'45'str'45'wf_960 v21
      C_valid'45'buffer'45'wf_972 v21
        -> coe C_valid'45'buffer'45'wf_972 v21
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pl-eq
d_pl'45'eq_6016 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'eq_6016 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.spl-eq
d_spl'45'eq_6018 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_spl'45'eq_6018 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_6020 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_6020 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_6022 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_6022 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_6024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 -> AgdaAny -> AgdaAny -> T_ValidAtWF_570
d_fv''_6024 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 v23 ~v24 ~v25 ~v26 ~v27 v28
            ~v29 ~v30 v31 ~v32 ~v33 ~v34 v35 ~v36
  = du_fv''_6024
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v21 v23 v28 v31 v35
du_fv''_6024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
du_fv''_6024 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_6026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 -> AgdaAny -> AgdaAny -> T_ValidAtWF_570
d_sv''_6026 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 v22 ~v23 v24 ~v25 ~v26 ~v27 ~v28
            v29 ~v30 ~v31 v32 ~v33 ~v34 ~v35 v36
  = du_sv''_6026
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v20 v22 v24 v29 v32 v36
du_sv''_6026 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
du_sv''_6026 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cl-eq
d_cl'45'eq_6090 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cl'45'eq_6090 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.scl-eq
d_scl'45'eq_6092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scl'45'eq_6092 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_6094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_6094 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_6096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_6096 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_6098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_BodyCorrect_750 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 -> AgdaAny -> T_ValidAtWF_570
d_ev''_6098 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 ~v19 ~v20 v21 ~v22 v23 v24 ~v25 ~v26 ~v27 ~v28
            v29 ~v30 v31 ~v32 ~v33 ~v34 v35
  = du_ev''_6098
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v21 v23 v24 v29 v31 v35
du_ev''_6098 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
du_ev''_6098 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_6236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 -> T_LocInRegions_5580 -> AgdaAny -> AgdaAny
d_tg''_6236 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_6238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_6238 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_6240 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_6240 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_6242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 -> AgdaAny -> T_ValidAtWF_570
d_pv''_6242 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_6242
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v20 v21 v25 v27 v30
du_pv''_6242 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
du_pv''_6242 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_6296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 -> T_LocInRegions_5580 -> AgdaAny -> AgdaAny
d_tg''_6296 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_6298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_6298 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_6300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_6300 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_6302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
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
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 ->
  T_LocInRegions_5580 ->
  T_LocInRegions_5580 -> AgdaAny -> T_ValidAtWF_570
d_pv''_6302 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_6302
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v19 v20 v21 v25 v27 v30
du_pv''_6302 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny -> T_ValidAtWF_570
du_pv''_6302 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_5938
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_6460 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'mem'45'preserved'45'in'45'regions_6460 ~v0 ~v1 ~v2
                                                       ~v3 ~v4
  = du_validityWF'45'mem'45'preserved'45'in'45'regions_6460
du_validityWF'45'mem'45'preserved'45'in'45'regions_6460 ::
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
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'mem'45'preserved'45'in'45'regions_6460
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_6466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_reclaim'45'alloc_6466 ~v0 ~v1 ~v2 v3 v4
  = du_reclaim'45'alloc_6466 v3 v4
du_reclaim'45'alloc_6466 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_reclaim'45'alloc_6466 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_6480 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_reclaim'45'preserves'45'frontier_6480 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                        v7
  = du_reclaim'45'preserves'45'frontier_6480 v5 v6 v7
du_reclaim'45'preserves'45'frontier_6480 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_reclaim'45'preserves'45'frontier_6480 v0 v1 v2
  = coe
      du_stack'45'alloc'45'advances''_6504 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.stack-alloc-advances'
d_stack'45'alloc'45'advances''_6504 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_stack'45'alloc'45'advances''_6504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10 v11 v12
  = du_stack'45'alloc'45'advances''_6504 v10 v11 v12
du_stack'45'alloc'45'advances''_6504 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_stack'45'alloc'45'advances''_6504 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_666 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_666
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v8) (coe v0))
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_676 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_676 v7
                    v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680 v5
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_6564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
d_validityWF'45'reclaim_6564 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             ~v11 v12
  = du_validityWF'45'reclaim_6564 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v12
du_validityWF'45'reclaim_6564 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'reclaim_6564 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'frontier'45'advance_4366 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v3)))
      (coe du_reclaim'45'alloc_6466 (coe v3) (coe v8)) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v9)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v3)))
      (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_6598 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
d_derive'45'mem'45'preserved'45'at_6598 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.k<start
d_k'60'start_6626 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'start_6626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 v13
  = du_k'60'start_6626 v12 v13
du_k'60'start_6626 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'start_6626 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_6670 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_6670 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_6704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  T_ValidAtWF_570 -> AgdaAny -> AgdaAny -> T_ValidAtWF_570
d_validityWF'45'trace'45'preserves_6704 v0 v1 v2 ~v3 v4 v5 v6 v7
                                        ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_validityWF'45'trace'45'preserves_6704
      v0 v1 v2 v4 v5 v6 v7 v9 v11
du_validityWF'45'trace'45'preserves_6704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_570 -> T_ValidAtWF_570
du_validityWF'45'trace'45'preserves_6704 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validityWF'45'mem'45'preserved_5120 (coe v0) (coe v1) (coe v2)
      (coe v4) (coe v3) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2866 (coe v1)
            (coe v5) (coe v7) (coe v4)))
      (coe v8)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_6742 ::
  T_IRResultAWF_680 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_6742 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_6754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
d_mem'45'preserved'45'from'45'tnhw_6754 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_6786 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
d_before'45'frontier'45'monotone_6786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7 v8 v9
  = du_before'45'frontier'45'monotone_6786 v7 v8 v9
du_before'45'frontier'45'monotone_6786 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
du_before'45'frontier'45'monotone_6786 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_666 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_666
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v6) (coe v0))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_676 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_676 v5
             v6 v7 v8
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680 v4
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_680
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_6868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
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
d_mem'45'preserved'45'compose_6868 = erased
