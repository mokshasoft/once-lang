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
import qualified MAlonzo.Code.Agda.Builtin.Float
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286]
d_ir'45'to'45'trace'45'at'45'frontier_12 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'at'45'frontier_692
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump
d_AllocBump_26 a0 a1 a2 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.BeforeFrontier
d_BeforeFrontier_30 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.apply-bump
d_apply'45'bump_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_apply'45'bump_34 ~v0 ~v1 ~v2 = du_apply'45'bump_34
du_apply'45'bump_34 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_apply'45'bump_34
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_924
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_76 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 -> Integer
d_next'45'heap'45'ref'45'delta_76 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_920
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_78 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 -> Integer
d_next'45'slot'45'delta_78 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_918
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.readLoc
d_readLoc_104 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_104 ~v0 ~v1 ~v2 = du_readLoc_104
du_readLoc_104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_104
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.write-loc
d_write'45'loc_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_write'45'loc_142 ~v0 v1 ~v2 = du_write'45'loc_142 v1
du_write'45'loc_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_write'45'loc_142 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_write'45'loc_324
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.exec-trace
d_exec'45'trace_202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_202 ~v0 v1 ~v2 = du_exec'45'trace_202 v1
du_exec'45'trace_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_202 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2872 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.TraceWF
d_TraceWF_260 a0 a1 a2 a3 a4 a5 = ()
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
d_SumTag_498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_498 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_522 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_522 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.prim-sv
d_prim'45'sv_534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_prim'45'sv_534 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_prim'45'sv_534 v4 v5
du_prim'45'sv_534 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_prim'45'sv_534 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_512
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78
             (coe MAlonzo.Code.Once.Type.C_Int_136)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe v1)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_514
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78
             (coe MAlonzo.Code.Once.Type.C_Float_138)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_200) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_542 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ValidAtWF_542
  = C_valid'45'unit'45'wf_778 |
    C_valid'45'pair'45'wf_804 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.IR.T_AllocMode_4
                              MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                              T_ValidAtWF_542 T_ValidAtWF_542 |
    C_valid'45'closure'45'wf_834 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                                 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                 MAlonzo.Code.Once.IR.T_AllocMode_4
                                 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                                 T_ValidAtWF_542 T_BodyCorrect_768 |
    C_valid'45'inl'45'wf_854 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                             T_ValidAtWF_542 |
    C_valid'45'inr'45'wf_874 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                             T_ValidAtWF_542 |
    C_valid'45'μ'45'wf_890 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                           T_ValidAtWF_542 |
    C_valid'45'ν'45'wf_906 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                           T_ValidAtWF_542 |
    C_valid'45'int'45'wf_918 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 |
    C_valid'45'float'45'wf_930 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 |
    C_valid'45'str'45'wf_942 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 |
    C_valid'45'buffer'45'wf_954 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_558 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ValidAtWF_542
d_valid'45'primitive'45'wf_558 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9 v10 ~v11
  = du_valid'45'primitive'45'wf_558 v9 v10
du_valid'45'primitive'45'wf_558 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542
du_valid'45'primitive'45'wf_558 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_512
        -> coe C_valid'45'int'45'wf_918 v1
      MAlonzo.Code.Once.IRTy.C_fits'45'float_514
        -> coe C_valid'45'float'45'wf_930 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ResultPlace
d_ResultPlace_572 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ResultPlace_572
  = C_unit'45'result_972 |
    C_at'45'loc_988 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                    T_ValidAtWF_542
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                    T_ValidAtWF_542
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 |
    C_at'45'reg_1006 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                     MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-loc
d_place'45'loc_586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_place'45'loc_586 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_place'45'loc_586 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_place'45'loc_586 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_place'45'loc_586 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_972
        -> coe
             seq (coe v3)
             (coe d_unit'45'result'45'loc'45'stub_1016 v0 v1 v2 v4 v5 v6 v7)
      C_at'45'loc_988 v15 v16 v17 v19 v20 -> coe v15
      C_at'45'reg_1006 v15 v16 v17 v19 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-before
d_place'45'before_602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_place'45'before_602 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_place'45'before_602 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_place'45'before_602 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_place'45'before_602 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_972
        -> coe
             seq (coe v3) (coe d_before'45'stub_1028 v0 v1 v2 v4 v5 v6 v7)
      C_at'45'loc_988 v15 v16 v17 v19 v20 -> coe v17
      C_at'45'reg_1006 v15 v16 v17 v19 -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-sv
d_place'45'sv_616 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_place'45'sv_616 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_unit'45'result_972
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72
                (coe d_unit'45'result'45'sv'45'loc_1040 v0 v1 v2 v4 v5 v6 v8))
      C_at'45'loc_988 v16 v17 v18 v20 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 (coe v16)
      C_at'45'reg_1006 v16 v17 v18 v20
        -> coe du_prim'45'sv_534 (coe v17) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-rax
d_place'45'rax_632 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_632 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-cont-before
d_place'45'cont'45'before_648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_place'45'cont'45'before_648 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_place'45'cont'45'before_648 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_place'45'cont'45'before_648 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_place'45'cont'45'before_648 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_972
        -> coe seq (coe v3) (coe d_before'45'cs_1064 v0 v1 v2 v4 v5 v6 v7)
      C_at'45'loc_988 v15 v16 v17 v19 v20 -> coe v20
      C_at'45'reg_1006 v15 v16 v17 v19 -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase
d_IRResultBase_664 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultBase_664
  = C_constructor_1144 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286]
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912
                       T_ResultPlace_572
                       MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424 AgdaAny
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_674 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IRStackBudget_674
  = C_constructor_1216 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.Sum.Base.T__'8846'__30)
                       AgdaAny AgdaAny AgdaAny AgdaAny Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget
d_IRHeapBudget_682 a0 a1 a2 a3 a4 a5 = ()
data T_IRHeapBudget_682
  = C_constructor_1246 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_698 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultAWF_698
  = C_constructor_1348 T_IRResultBase_664 T_IRStackBudget_674
                       T_IRHeapBudget_682
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  T_IRStackBudget_674 -> T_IRHeapBudget_682 -> T_IRResultAWF_698
d_mk'45'IRResultAWF'45'via'45'bump_752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
                                       ~v20 v21 ~v22 v23 v24 v25
  = du_mk'45'IRResultAWF'45'via'45'bump_752
      v10 v12 v13 v18 v21 v23 v24 v25
du_mk'45'IRResultAWF'45'via'45'bump_752 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  T_ResultPlace_572 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424 ->
  AgdaAny ->
  T_IRStackBudget_674 -> T_IRHeapBudget_682 -> T_IRResultAWF_698
du_mk'45'IRResultAWF'45'via'45'bump_752 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1348 (coe C_constructor_1144 v0 v1 v2 v3 v4 v5)
      (coe v6) (coe v7)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_768 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_BodyCorrect_768
  = C_constructor_1448 Integer
                       (AgdaAny ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        T_ValidAtWF_542 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-loc-stub
d_unit'45'result'45'loc'45'stub_1016
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-loc-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-stub
d_before'45'stub_1028
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc
d_unit'45'result'45'sv'45'loc_1040
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub
d_rax'45'stub_1052
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-cs
d_before'45'cs_1064
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-cs"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_1110 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_final'45'state_1110 v0
  = case coe v0 of
      C_constructor_1144 v1 v2 v3 v7 v10 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace
d_trace_1112 ::
  T_IRResultBase_664 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286]
d_trace_1112 v0
  = case coe v0 of
      C_constructor_1144 v1 v2 v3 v7 v10 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.bump
d_bump_1114 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912
d_bump_1114 v0
  = case coe v0 of
      C_constructor_1144 v1 v2 v3 v7 v10 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1116 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1116 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_1118 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1118 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_1120 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1120 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_1122 :: T_IRResultBase_664 -> T_ResultPlace_572
d_result'45'place_1122 v0
  = case coe v0 of
      C_constructor_1144 v1 v2 v3 v7 v10 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_1124 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1124 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_1128 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1128 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_1130 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424
d_trace'45'twf_1130 v0
  = case coe v0 of
      C_constructor_1144 v1 v2 v3 v7 v10 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_1136 ::
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1136 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1138 :: T_IRResultBase_664 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1138 v0
  = case coe v0 of
      C_constructor_1144 v1 v2 v3 v7 v10 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_1140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_final'45'alloc_1140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1140 v9 v10
du_final'45'alloc_1140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultBase_664 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_final'45'alloc_1140 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_924
      (coe d_bump_1114 (coe v1)) (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_1142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultBase_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1142 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_1182 :: T_IRStackBudget_674 -> Integer
d_max'45'slot'45'written_1182 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_1184 :: T_IRStackBudget_674 -> Integer
d_stack'45'budget_1184 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1186 ::
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1186 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1188 ::
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1188 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1190 ::
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1190 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_1196 ::
  T_IRStackBudget_674 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1196 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_1198 :: T_IRStackBudget_674 -> AgdaAny
d_trace'45'writes'45'above_1198 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1200 ::
  T_IRStackBudget_674 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1200 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_1202 :: T_IRStackBudget_674 -> AgdaAny
d_trace'45'writes'45'below_1202 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1204 ::
  T_IRStackBudget_674 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1204 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_1206 :: T_IRStackBudget_674 -> Integer
d_scratch'45'budget_1206 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_1208 ::
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1208 v0
  = case coe v0 of
      C_constructor_1216 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_1210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1210 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_slot'45'monotone_1210 v3
du_slot'45'monotone_1210 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1210 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1212 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7
  = du_slot'45'stays'45'in'45'budget_1212 v3 v4 v7
du_slot'45'stays'45'in'45'budget_1212 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  T_IRStackBudget_674 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1212 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_918
         (coe v1))
      (d_stack'45'budget_1184 (coe v2))
      (d_bump'45'fits'45'stack'45'budget_1186 (coe v2))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_1234 :: T_IRHeapBudget_682 -> Integer
d_heap'45'budget_1234 v0
  = case coe v0 of
      C_constructor_1246 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1236 ::
  T_IRHeapBudget_682 -> Integer
d_max'45'heap'45'ref'45'written_1236 v0
  = case coe v0 of
      C_constructor_1246 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1238 ::
  T_IRHeapBudget_682 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1238 v0
  = case coe v0 of
      C_constructor_1246 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1240 ::
  T_IRHeapBudget_682 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1240 v0
  = case coe v0 of
      C_constructor_1246 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1242 ::
  T_IRHeapBudget_682 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1242 v0
  = case coe v0 of
      C_constructor_1246 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_1244 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_IRHeapBudget_682 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1244 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_heap'45'monotone_1244 v3
du_heap'45'monotone_1244 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1244 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.base
d_base_1268 :: T_IRResultAWF_698 -> T_IRResultBase_664
d_base_1268 v0
  = case coe v0 of
      C_constructor_1348 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_1270 :: T_IRResultAWF_698 -> T_IRStackBudget_674
d_stack'45'inv_1270 v0
  = case coe v0 of
      C_constructor_1348 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_1272 :: T_IRResultAWF_698 -> T_IRHeapBudget_682
d_heap'45'inv_1272 v0
  = case coe v0 of
      C_constructor_1348 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.alloc-correct
d_alloc'45'correct_1276 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1276 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump
d_bump_1278 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_912
d_bump_1278 v0 = coe d_bump_1114 (coe d_base_1268 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-alloc
d_final'45'alloc_1280 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_final'45'alloc_1280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1280 v9 v10
du_final'45'alloc_1280 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_final'45'alloc_1280 v0 v1
  = coe du_final'45'alloc_1140 (coe v0) (coe d_base_1268 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-state
d_final'45'state_1282 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_final'45'state_1282 v0
  = coe d_final'45'state_1110 (coe d_base_1268 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frame-preserved
d_frame'45'preserved_1284 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1284 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.mem-preserved-before
d_mem'45'preserved'45'before_1286 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1286 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.not-halted
d_not'45'halted_1288 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1288 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.result-place
d_result'45'place_1290 :: T_IRResultAWF_698 -> T_ResultPlace_572
d_result'45'place_1290 v0
  = coe d_result'45'place_1122 (coe d_base_1268 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace
d_trace_1292 ::
  T_IRResultAWF_698 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286]
d_trace_1292 v0 = coe d_trace_1112 (coe d_base_1268 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-correct
d_trace'45'correct_1294 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1294 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1296 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1296 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1298 :: T_IRResultAWF_698 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1298 v0
  = coe d_trace'45'no'45'frame'45'ops_1138 (coe d_base_1268 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-preserves-halted
d_trace'45'preserves'45'halted_1300 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1300 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-twf
d_trace'45'twf_1302 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8424
d_trace'45'twf_1302 v0
  = coe d_trace'45'twf_1130 (coe d_base_1268 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1306 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1306 v0
  = coe
      d_bump'45'fits'45'stack'45'budget_1186
      (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frontier-slot-stable
d_frontier'45'slot'45'stable_1308 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1308 v0
  = coe
      d_frontier'45'slot'45'stable_1196
      (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1310 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1310 v0
  = coe
      d_max'45'slot'45'geq'45'final_1188
      (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1312 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1312 v0
  = coe
      d_max'45'slot'45'usage'45'bound_1190
      (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-written
d_max'45'slot'45'written_1314 :: T_IRResultAWF_698 -> Integer
d_max'45'slot'45'written_1314 v0
  = coe
      d_max'45'slot'45'written_1182 (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-bounded
d_scratch'45'bounded_1316 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1316 v0
  = coe d_scratch'45'bounded_1208 (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-budget
d_scratch'45'budget_1318 :: T_IRResultAWF_698 -> Integer
d_scratch'45'budget_1318 v0
  = coe d_scratch'45'budget_1206 (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-monotone
d_slot'45'monotone_1320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_1320 v9
du_slot'45'monotone_1320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1320 v0 = coe du_slot'45'monotone_1210 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1322 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_1322 v9 v10
du_slot'45'stays'45'in'45'budget_1322 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1322 v0 v1
  = coe
      du_slot'45'stays'45'in'45'budget_1212 (coe v0)
      (coe d_bump_1114 (coe d_base_1268 (coe v1)))
      (coe d_stack'45'inv_1270 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.stack-budget
d_stack'45'budget_1324 :: T_IRResultAWF_698 -> Integer
d_stack'45'budget_1324 v0
  = coe d_stack'45'budget_1184 (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1326 ::
  T_IRResultAWF_698 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1326 v0
  = coe
      d_trace'45'slot'45'reads'45'above_1200
      (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1328 ::
  T_IRResultAWF_698 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1328 v0
  = coe
      d_trace'45'slot'45'reads'45'below_1204
      (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-above
d_trace'45'writes'45'above_1330 :: T_IRResultAWF_698 -> AgdaAny
d_trace'45'writes'45'above_1330 v0
  = coe
      d_trace'45'writes'45'above_1198 (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-below
d_trace'45'writes'45'below_1332 :: T_IRResultAWF_698 -> AgdaAny
d_trace'45'writes'45'below_1332 v0
  = coe
      d_trace'45'writes'45'below_1202 (coe d_stack'45'inv_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1336 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1336 v0
  = coe
      d_bump'45'fits'45'heap'45'budget_1238
      (coe d_heap'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-budget
d_heap'45'budget_1338 :: T_IRResultAWF_698 -> Integer
d_heap'45'budget_1338 v0
  = coe d_heap'45'budget_1234 (coe d_heap'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-monotone
d_heap'45'monotone_1340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_1340 v9
du_heap'45'monotone_1340 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1340 v0 = coe du_heap'45'monotone_1244 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1342 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1342 v0
  = coe
      d_max'45'heap'45'ref'45'geq'45'final_1240
      (coe d_heap'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1344 ::
  T_IRResultAWF_698 -> Integer
d_max'45'heap'45'ref'45'written_1344 v0
  = coe
      d_max'45'heap'45'ref'45'written_1236
      (coe d_heap'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1346 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1346 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1242
      (coe d_heap'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_1428 :: T_BodyCorrect_768 -> Integer
d_body'45'capacity_1428 v0
  = case coe v0 of
      C_constructor_1448 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_1430 ::
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_1430 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.execute
d_execute_1446 ::
  T_BodyCorrect_768 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_1446 v0
  = case coe v0 of
      C_constructor_1448 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_1466 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_1466 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-via-budget
d_bound'45'via'45'budget_1478 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'via'45'budget_1478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 v10 ~v11
  = du_bound'45'via'45'budget_1478 v10
du_bound'45'via'45'budget_1478 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'via'45'budget_1478 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1242
      (coe d_heap'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-alloc
d_bound'45'alloc_1482 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_698 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'alloc_1482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      ~v11
  = du_bound'45'alloc_1482 v10
du_bound'45'alloc_1482 ::
  T_IRResultAWF_698 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'alloc_1482 v0
  = coe du_bound'45'via'45'budget_1478 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_1508 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13
  = ()
data T_ClosureWellFormed_1508
  = C_constructor_1564 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.IR.T_AllocMode_4 T_ValidAtWF_542
                       T_BodyCorrect_768
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_1548 ::
  T_ClosureWellFormed_1508 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1548 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_1550 ::
  T_ClosureWellFormed_1508 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1550 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_1552 ::
  T_ClosureWellFormed_1508 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_env'45'before_1552 v0
  = case coe v0 of
      C_constructor_1564 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_1554 ::
  T_ClosureWellFormed_1508 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_code'45'before_1554 v0
  = case coe v0 of
      C_constructor_1564 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_1556 ::
  T_ClosureWellFormed_1508 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_1556 v0
  = case coe v0 of
      C_constructor_1564 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_1558 ::
  T_ClosureWellFormed_1508 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1558 v0
  = case coe v0 of
      C_constructor_1564 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_1560 :: T_ClosureWellFormed_1508 -> T_ValidAtWF_542
d_env'45'valid_1560 v0
  = case coe v0 of
      C_constructor_1564 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_1562 ::
  T_ClosureWellFormed_1508 -> T_BodyCorrect_768
d_body'45'correct_1562 v0
  = case coe v0 of
      C_constructor_1564 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_1578 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ClosureValidWF_1578
  = C_constructor_1652 MAlonzo.Code.Once.IRTy.T_IRTy_6
                       MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       T_ValidAtWF_542 T_BodyCorrect_768
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_1622 ::
  T_ClosureValidWF_1578 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1622 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body
d_body_1624 ::
  T_ClosureValidWF_1578 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1624 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env
d_env_1626 :: T_ClosureValidWF_1578 -> AgdaAny
d_env_1626 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body<bound
d_body'60'bound_1628 ::
  T_ClosureValidWF_1578 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_1628 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-loc
d_env'45'loc_1630 ::
  T_ClosureValidWF_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_1630 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_1632 ::
  T_ClosureValidWF_1578 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_1632 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.mEnv
d_mEnv_1634 ::
  T_ClosureValidWF_1578 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1634 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-ptr
d_env'45'ptr_1636 ::
  T_ClosureValidWF_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1636 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_1638 ::
  T_ClosureValidWF_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1638 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-before
d_env'45'before_1640 ::
  T_ClosureValidWF_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_env'45'before_1640 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1642 ::
  T_ClosureValidWF_1578 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_1642 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-valid
d_env'45'valid_1644 :: T_ClosureValidWF_1578 -> T_ValidAtWF_542
d_env'45'valid_1644 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-correct
d_body'45'correct_1646 ::
  T_ClosureValidWF_1578 -> T_BodyCorrect_768
d_body'45'correct_1646 v0
  = case coe v0 of
      C_constructor_1652 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1650 ::
  T_ClosureValidWF_1578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1650 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_1668 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_ClosureValidWF_1578
d_decomposeClosureWF_1668 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10
  = du_decomposeClosureWF_1668 v10
du_decomposeClosureWF_1668 ::
  T_ValidAtWF_542 -> T_ClosureValidWF_1578
du_decomposeClosureWF_1668 v0
  = case coe v0 of
      C_valid'45'closure'45'wf_834 v2 v5 v6 v8 v10 v12 v13 v14 v17 v18 v19 v20
        -> coe C_constructor_1652 v2 v5 v6 v8 v10 v13 v12 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_1698 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> Integer -> ()
d_RecDispatcherWF_1698 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF
d_PairValidWF_1732 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_PairValidWF_1732
  = C_constructor_1790 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       T_ValidAtWF_542 T_ValidAtWF_542
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-loc
d_fst'45'loc_1768 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_1768 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-loc
d_snd'45'loc_1770 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_1770 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mA
d_mA_1772 ::
  T_PairValidWF_1732 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1772 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mB
d_mB_1774 ::
  T_PairValidWF_1732 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1774 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-ptr
d_fst'45'ptr_1776 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_1776 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-ptr
d_snd'45'ptr_1778 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_1778 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-before
d_fst'45'before_1780 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_fst'45'before_1780 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-before
d_snd'45'before_1782 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_snd'45'before_1782 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_1784 ::
  T_PairValidWF_1732 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_1784 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-valid
d_fst'45'valid_1786 :: T_PairValidWF_1732 -> T_ValidAtWF_542
d_fst'45'valid_1786 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-valid
d_snd'45'valid_1788 :: T_PairValidWF_1732 -> T_ValidAtWF_542
d_snd'45'valid_1788 v0
  = case coe v0 of
      C_constructor_1790 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_1806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_PairValidWF_1732
d_decomposePairWF_1806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_decomposePairWF_1806 v10
du_decomposePairWF_1806 :: T_ValidAtWF_542 -> T_PairValidWF_1732
du_decomposePairWF_1806 v0
  = case coe v0 of
      C_valid'45'pair'45'wf_804 v8 v9 v11 v12 v13 v16 v17 v18 v19 v20
        -> coe C_constructor_1790 v8 v9 v11 v12 v16 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF
d_InlValidWF_1844 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InlValidWF_1844
  = C_constructor_1890 AgdaAny MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       T_ValidAtWF_542
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.a
d_a_1874 :: T_InlValidWF_1844 -> AgdaAny
d_a_1874 v0
  = case coe v0 of
      C_constructor_1890 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.mA
d_mA_1876 ::
  T_InlValidWF_1844 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1876 v0
  = case coe v0 of
      C_constructor_1890 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-loc
d_payload'45'loc_1878 ::
  T_InlValidWF_1844 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_1878 v0
  = case coe v0 of
      C_constructor_1890 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-ptr
d_payload'45'ptr_1880 ::
  T_InlValidWF_1844 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_1880 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-before
d_payload'45'before_1882 ::
  T_InlValidWF_1844 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_payload'45'before_1882 v0
  = case coe v0 of
      C_constructor_1890 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_1884 ::
  T_InlValidWF_1844 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_1884 v0
  = case coe v0 of
      C_constructor_1890 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-valid
d_payload'45'valid_1886 :: T_InlValidWF_1844 -> T_ValidAtWF_542
d_payload'45'valid_1886 v0
  = case coe v0 of
      C_constructor_1890 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_1888 ::
  T_InlValidWF_1844 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_1888 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF
d_InrValidWF_1904 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InrValidWF_1904
  = C_constructor_1950 AgdaAny MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
                       T_ValidAtWF_542
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.b
d_b_1934 :: T_InrValidWF_1904 -> AgdaAny
d_b_1934 v0
  = case coe v0 of
      C_constructor_1950 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.mB
d_mB_1936 ::
  T_InrValidWF_1904 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1936 v0
  = case coe v0 of
      C_constructor_1950 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-loc
d_payload'45'loc_1938 ::
  T_InrValidWF_1904 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_1938 v0
  = case coe v0 of
      C_constructor_1950 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-ptr
d_payload'45'ptr_1940 ::
  T_InrValidWF_1904 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_1940 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-before
d_payload'45'before_1942 ::
  T_InrValidWF_1904 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_payload'45'before_1942 v0
  = case coe v0 of
      C_constructor_1950 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_1944 ::
  T_InrValidWF_1904 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sucLoc'45'before_1944 v0
  = case coe v0 of
      C_constructor_1950 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-valid
d_payload'45'valid_1946 :: T_InrValidWF_1904 -> T_ValidAtWF_542
d_payload'45'valid_1946 v0
  = case coe v0 of
      C_constructor_1950 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_1948 ::
  T_InrValidWF_1904 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_1948 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_1966 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_InlValidWF_1844
d_decomposeInlWF_1966 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInlWF_1966 v7 v10
du_decomposeInlWF_1966 ::
  AgdaAny -> T_ValidAtWF_542 -> T_InlValidWF_1844
du_decomposeInlWF_1966 v0 v1
  = case coe v1 of
      C_valid'45'inl'45'wf_854 v8 v10 v11 v14 v15 v16
        -> coe C_constructor_1890 v0 v10 v8 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_2002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_InrValidWF_1904
d_decomposeInrWF_2002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInrWF_2002 v7 v10
du_decomposeInrWF_2002 ::
  AgdaAny -> T_ValidAtWF_542 -> T_InrValidWF_1904
du_decomposeInrWF_2002 v0 v1
  = case coe v1 of
      C_valid'45'inr'45'wf_874 v8 v10 v11 v14 v15 v16
        -> coe C_constructor_1950 v0 v10 v8 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_2032 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542
d_valid'45'to'45'validWF'45'unit_2032 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_valid'45'to'45'validWF'45'unit_2032
du_valid'45'to'45'validWF'45'unit_2032 :: T_ValidAtWF_542
du_valid'45'to'45'validWF'45'unit_2032
  = coe C_valid'45'unit'45'wf_778
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_2048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'mem'45'only_2048 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9
                                 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'only_2048 v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'only_2048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'mem'45'only_2048 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_778))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2114 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v31))
                           (coe
                              du_sv''_2116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2210 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2254 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2166 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_890 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_890 v15
                    (coe
                       du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_906 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_906 v15
                    (coe
                       du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_918 v14 -> coe C_valid'45'int'45'wf_918 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_930 v14
               -> coe C_valid'45'float'45'wf_930 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_942 v14 -> coe C_valid'45'str'45'wf_942 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_954 v14
               -> coe C_valid'45'buffer'45'wf_954 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2110 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2112 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_fv''_2114 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_fv''_2114 v0 v1 v2 v4 v5 v7 v10 v11 v14 v16 v24
du_fv''_2114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_fv''_2114 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_sv''_2116 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_sv''_2116 v0 v1 v2 v4 v6 v8 v10 v11 v15 v17 v25
du_sv''_2116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_sv''_2116 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2162 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2162 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2164 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2164 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_BodyCorrect_768 -> T_ValidAtWF_542
d_ev''_2166 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            v14 ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_ev''_2166 v0 v1 v2 v4 v8 v9 v12 v14 v16 v17 v24
du_ev''_2166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_ev''_2166 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2206 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_2206 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2208 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_2210 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2210 v0 v1 v2 v4 v5 v8 v9 v12 v13 v14 v20
du_pv''_2210 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_2210 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2250 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_2250 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2252 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_2254 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2254 v0 v1 v2 v4 v6 v8 v9 v12 v13 v14 v20
du_pv''_2254 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_2254 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2048 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_2382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'write'45'at'45'frontier_2382 v0 v1 v2 ~v3 v4 v5 v6
                                             ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'frontier_2382
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'frontier_2382 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'write'45'at'45'frontier_2382 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_778)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2444 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_2446 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2536 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2578 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_890 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_890 v15
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_906 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_906 v15
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_918 v14 -> coe C_valid'45'int'45'wf_918 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_930 v14
               -> coe C_valid'45'float'45'wf_930 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_942 v14 -> coe C_valid'45'str'45'wf_942 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_954 v14
               -> coe C_valid'45'buffer'45'wf_954 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2440 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2440 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2442 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2442 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_fv''_2444 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2444 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_2444 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_fv''_2444 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_sv''_2446 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_2446 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_2446 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_sv''_2446 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2490 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2490 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2492 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2492 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_BodyCorrect_768 -> T_ValidAtWF_542
d_ev''_2494 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_2494 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_2494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_ev''_2494 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2532 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_2532 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2534 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2534 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_2536 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2536 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_2536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_2536 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2574 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_2574 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2576 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2576 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_2578 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2578 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_2578 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_2578 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2382 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_2694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'write'45'at'45'suc'45'frontier_2694 v0 v1 v2 ~v3 v4
                                                    v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'suc'45'frontier_2694
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'suc'45'frontier_2694 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'write'45'at'45'suc'45'frontier_2694 v0 v1 v2 v3 v4
                                                     v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_778)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2756 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_2758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2848 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2890 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_890 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_890 v15
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_906 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_906 v15
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_918 v14 -> coe C_valid'45'int'45'wf_918 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_930 v14
               -> coe C_valid'45'float'45'wf_930 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_942 v14 -> coe C_valid'45'str'45'wf_942 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_954 v14
               -> coe C_valid'45'buffer'45'wf_954 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2752 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2752 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2754 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2754 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_fv''_2756 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2756 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_2756 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_fv''_2756 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_sv''_2758 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_2758 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_2758 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_sv''_2758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2802 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2804 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2804 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_BodyCorrect_768 -> T_ValidAtWF_542
d_ev''_2806 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_2806 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_2806 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_ev''_2806 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_2844 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2846 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2846 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_2848 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2848 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_2848 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_2848 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_2886 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2888 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2888 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_2890 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2890 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_2890 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_2890 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2694 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_3008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'alloc'45'advance_3008 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
                                      v9 v10
  = du_validityWF'45'alloc'45'advance_3008
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10
du_validityWF'45'alloc'45'advance_3008 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer -> T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'alloc'45'advance_3008 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v9) (coe C_valid'45'unit'45'wf_778))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> case coe v9 of
                    C_valid'45'pair'45'wf_804 v21 v22 v24 v25 v26 v29 v30 v31 v32 v33
                      -> coe
                           C_valid'45'pair'45'wf_804 v21 v22 v24 v25 v26
                           (coe du_fb''_3062 (coe v3) (coe v21) (coe v29))
                           (coe du_sb''_3064 (coe v3) (coe v22) (coe v30))
                           (coe du_slb''_3066 (coe v3) (coe v6) (coe v31))
                           (coe
                              du_fv''_3068 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v7) (coe v8) (coe v21) (coe v24) (coe v32))
                           (coe
                              du_sv''_3070 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                              (coe v13) (coe v7) (coe v8) (coe v22) (coe v25) (coe v33))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
        -> case coe v9 of
             C_valid'45'inl'45'wf_854 v18 v20 v21 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v27
                      -> coe
                           C_valid'45'inl'45'wf_854 v18 v20 v21
                           (coe du_pb''_3152 (coe v3) (coe v18) (coe v24))
                           (coe du_slb''_3154 (coe v3) (coe v6) (coe v25))
                           (coe
                              du_pv''_3156 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v7)
                              (coe v8) (coe v27) (coe v18) (coe v20) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v18 v20 v21 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v27
                      -> coe
                           C_valid'45'inr'45'wf_874 v18 v20 v21
                           (coe du_pb''_3192 (coe v3) (coe v18) (coe v24))
                           (coe du_slb''_3194 (coe v3) (coe v6) (coe v25))
                           (coe
                              du_pv''_3196 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v7)
                              (coe v8) (coe v27) (coe v18) (coe v20) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
        -> case coe v9 of
             C_valid'45'closure'45'wf_834 v13 v16 v17 v19 v21 v23 v24 v25 v28 v29 v30 v31
               -> coe
                    C_valid'45'closure'45'wf_834 v13 v16 v17 v19 v21 v23 v24 v25
                    (coe du_eb''_3112 (coe v3) (coe v21) (coe v28))
                    (coe du_slb''_3114 (coe v3) (coe v6) (coe v29))
                    (coe
                       du_ev''_3116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                       (coe v13) (coe v17) (coe v21) (coe v23) (coe v30))
                    v31
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
        -> case coe v9 of
             C_valid'45'μ'45'wf_890 v16 v18
               -> coe
                    C_valid'45'μ'45'wf_890 v16
                    (coe
                       du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v16) (coe v5))
                       (coe v6) (coe v7) (coe v8) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
        -> case coe v9 of
             C_valid'45'ν'45'wf_906 v16 v18
               -> coe
                    C_valid'45'ν'45'wf_906 v16
                    (coe
                       du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v16) (coe v5))
                       (coe v6) (coe v7) (coe v8) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v9 of
             C_valid'45'int'45'wf_918 v15
               -> coe
                    C_valid'45'int'45'wf_918
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v9 of
             C_valid'45'float'45'wf_930 v15
               -> coe
                    C_valid'45'float'45'wf_930
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v9 of
             C_valid'45'str'45'wf_942 v15
               -> coe
                    C_valid'45'str'45'wf_942
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v9 of
             C_valid'45'buffer'45'wf_954 v15
               -> coe
                    C_valid'45'buffer'45'wf_954
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_3062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_fb''_3062 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23
  = du_fb''_3062 v4 v12 v19
du_fb''_3062 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_fb''_3062 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_3064 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sb''_3064 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_sb''_3064 v4 v13 v20
du_sb''_3064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_sb''_3064 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3066 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3066 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_slb''_3066 v4 v9 v21
du_slb''_3066 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3066 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_fv''_3068 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_fv''_3068 v0 v1 v2 v4 v5 v7 v10 v11 v12 v14 v22
du_fv''_3068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_fv''_3068 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v8) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_sv''_3070 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_sv''_3070 v0 v1 v2 v4 v6 v8 v10 v11 v13 v15 v23
du_sv''_3070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_sv''_3070 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v8) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_3112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_eb''_3112 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_eb''_3112 v4 v14 v20
du_eb''_3112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_eb''_3112 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3114 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_slb''_3114 v4 v7 v21
du_slb''_3114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_BodyCorrect_768 -> T_ValidAtWF_542
d_ev''_3116 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_ev''_3116 v0 v1 v2 v4 v8 v9 v10 v12 v14 v15 v22
du_ev''_3116 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_ev''_3116 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v8) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3152 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_pb''_3152 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_3152 v4 v11 v16
du_pb''_3152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_pb''_3152 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3154 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3154 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_3154 v4 v7 v17
du_slb''_3154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3154 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_3156 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_3156 v0 v1 v2 v4 v5 v8 v9 v10 v11 v12 v18
du_pv''_3156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_3156 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v8) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3192 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_pb''_3192 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_3192 v4 v11 v16
du_pb''_3192 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_pb''_3192 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3194 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3194 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_3194 v4 v7 v17
du_slb''_3194 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3194 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_780
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_3196 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_3196 v0 v1 v2 v4 v6 v8 v9 v10 v11 v12 v18
du_pv''_3196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_3196 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3008 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v8) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_3300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'frontier'45'advance_3300 v0 v1 v2 ~v3 v4 v5 v6 v7
                                         v8 v9 ~v10 v11 v12 v13
  = du_validityWF'45'frontier'45'advance_3300
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_validityWF'45'frontier'45'advance_3300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'frontier'45'advance_3300 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 v11
  = case coe v5 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v6) (coe seq (coe v11) (coe C_valid'45'unit'45'wf_778))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
               -> case coe v11 of
                    C_valid'45'pair'45'wf_804 v23 v24 v26 v27 v28 v31 v32 v33 v34 v35
                      -> coe
                           C_valid'45'pair'45'wf_804 v23 v24 v26 v27 v28
                           (coe du_fb''_3366 (coe v9) (coe v10) (coe v23) (coe v31))
                           (coe du_sb''_3368 (coe v9) (coe v10) (coe v24) (coe v32))
                           (coe du_slb''_3370 (coe v7) (coe v9) (coe v10) (coe v33))
                           (coe
                              du_fv''_3372 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                              (coe v14) (coe v8) (coe v9) (coe v10) (coe v23) (coe v26)
                              (coe v34))
                           (coe
                              du_sv''_3374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
                              (coe v15) (coe v8) (coe v9) (coe v10) (coe v24) (coe v27)
                              (coe v35))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
        -> case coe v11 of
             C_valid'45'inl'45'wf_854 v20 v22 v23 v26 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                      -> coe
                           C_valid'45'inl'45'wf_854 v20 v22 v23
                           (coe du_pb''_3468 (coe v9) (coe v10) (coe v20) (coe v26))
                           (coe du_slb''_3470 (coe v7) (coe v9) (coe v10) (coe v27))
                           (coe
                              du_pv''_3472 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                              (coe v8) (coe v9) (coe v10) (coe v29) (coe v20) (coe v22)
                              (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v20 v22 v23 v26 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                      -> coe
                           C_valid'45'inr'45'wf_874 v20 v22 v23
                           (coe du_pb''_3514 (coe v9) (coe v10) (coe v20) (coe v26))
                           (coe du_slb''_3516 (coe v7) (coe v9) (coe v10) (coe v27))
                           (coe
                              du_pv''_3518 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
                              (coe v8) (coe v9) (coe v10) (coe v29) (coe v20) (coe v22)
                              (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v12 v13
        -> case coe v11 of
             C_valid'45'closure'45'wf_834 v15 v18 v19 v21 v23 v25 v26 v27 v30 v31 v32 v33
               -> coe
                    C_valid'45'closure'45'wf_834 v15 v18 v19 v21 v23 v25 v26 v27
                    (coe du_eb''_3422 (coe v9) (coe v10) (coe v23) (coe v30))
                    (coe du_slb''_3424 (coe v7) (coe v9) (coe v10) (coe v31))
                    (coe
                       du_ev''_3426 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                       (coe v9) (coe v10) (coe v15) (coe v19) (coe v23) (coe v25)
                       (coe v32))
                    v33
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
        -> case coe v11 of
             C_valid'45'μ'45'wf_890 v18 v20
               -> coe
                    C_valid'45'μ'45'wf_890 v18
                    (coe
                       du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v5)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v18) (coe v6))
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
        -> case coe v11 of
             C_valid'45'ν'45'wf_906 v18 v20
               -> coe
                    C_valid'45'ν'45'wf_906 v18
                    (coe
                       du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v5)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v18) (coe v6))
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v11 of
             C_valid'45'int'45'wf_918 v17
               -> coe
                    C_valid'45'int'45'wf_918
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v11 of
             C_valid'45'float'45'wf_930 v17
               -> coe
                    C_valid'45'float'45'wf_930
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v11 of
             C_valid'45'str'45'wf_942 v17
               -> coe
                    C_valid'45'str'45'wf_942
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v11 of
             C_valid'45'buffer'45'wf_954 v17
               -> coe
                    C_valid'45'buffer'45'wf_954
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_3366 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_fb''_3366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_fb''_3366 v13 v14 v15 v22
du_fb''_3366 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_fb''_3366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_3368 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_sb''_3368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25 ~v26
  = du_sb''_3368 v13 v14 v16 v23
du_sb''_3368 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_sb''_3368 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25 ~v26
  = du_slb''_3370 v10 v13 v14 v24
du_slb''_3370 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_fv''_3372 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 ~v9 ~v10 v11 ~v12 v13 v14
            v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
  = du_fv''_3372 v0 v1 v2 v4 v5 v6 v8 v11 v13 v14 v15 v17 v25
du_fv''_3372 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_fv''_3372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10) (coe v7)
      (coe v8) (coe v9) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_sv''_3374 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 ~v12 v13 v14
            ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
  = du_sv''_3374 v0 v1 v2 v4 v5 v7 v9 v11 v13 v14 v16 v18 v26
du_sv''_3374 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_sv''_3374 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10) (coe v7)
      (coe v8) (coe v9) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_3422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_eb''_3422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25 ~v26
  = du_eb''_3422 v11 v12 v17 v23
du_eb''_3422 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_eb''_3422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
             ~v26
  = du_slb''_3424 v8 v11 v12 v24
du_slb''_3424 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3424 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_BodyCorrect_768 -> T_ValidAtWF_542
d_ev''_3426 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
  = du_ev''_3426 v0 v1 v2 v4 v5 v9 v11 v12 v13 v15 v17 v18 v25
du_ev''_3426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_ev''_3426 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v10) (coe v5)
      (coe v6) (coe v7) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3468 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_pb''_3468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_3468 v11 v12 v14 v19
du_pb''_3468 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_pb''_3468 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_3470 v8 v11 v12 v20
du_slb''_3470 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3470 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_3472 v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_3472 v0 v1 v2 v4 v5 v6 v9 v11 v12 v13 v14 v15 v21
du_pv''_3472 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_3472 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v10) (coe v6)
      (coe v7) (coe v8) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3514 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_pb''_3514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_3514 v11 v12 v14 v19
du_pb''_3514 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_pb''_3514 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3516 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_slb''_3516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_3516 v8 v11 v12 v20
du_slb''_3516 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_slb''_3516 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_850
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_3518 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_3518 v0 v1 v2 v4 v5 v7 v9 v11 v12 v13 v14 v15 v21
du_pv''_3518 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_3518 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v10) (coe v6)
      (coe v7) (coe v8) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_3662 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646) ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'with'45'bf'45'transfer_3662 ~v0 ~v1 ~v2 ~v3 v4 v5
                                            v6 ~v7 ~v8 ~v9 v10 v11
  = du_validityWF'45'with'45'bf'45'transfer_3662 v4 v5 v6 v10 v11
du_validityWF'45'with'45'bf'45'transfer_3662 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646) ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'with'45'bf'45'transfer_3662 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v1) (coe seq (coe v4) (coe C_valid'45'unit'45'wf_778))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v4 of
                    C_valid'45'pair'45'wf_804 v16 v17 v19 v20 v21 v24 v25 v26 v27 v28
                      -> coe
                           C_valid'45'pair'45'wf_804 v16 v17 v19 v20 v21 (coe v3 v16 v24)
                           (coe v3 v17 v25)
                           (coe
                              v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                              v26)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3662 (coe v5) (coe v7)
                              (coe v16) (coe v3) (coe v27))
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3662 (coe v6) (coe v8)
                              (coe v17) (coe v3) (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v5 v6
        -> case coe v4 of
             C_valid'45'inl'45'wf_854 v13 v15 v16 v19 v20 v21
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
                      -> coe
                           C_valid'45'inl'45'wf_854 v13 v15 v16 (coe v3 v13 v19)
                           (coe
                              v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                              v20)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3662 (coe v5) (coe v22)
                              (coe v13) (coe v3) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v13 v15 v16 v19 v20 v21
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
                      -> coe
                           C_valid'45'inr'45'wf_874 v13 v15 v16 (coe v3 v13 v19)
                           (coe
                              v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                              v20)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3662 (coe v6) (coe v22)
                              (coe v13) (coe v3) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v5 v6
        -> case coe v4 of
             C_valid'45'closure'45'wf_834 v8 v11 v12 v14 v16 v18 v19 v20 v23 v24 v25 v26
               -> coe
                    C_valid'45'closure'45'wf_834 v8 v11 v12 v14 v16 v18 v19 v20
                    (coe v3 v16 v23)
                    (coe
                       v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                       v24)
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3662 (coe v8) (coe v12)
                       (coe v16) (coe v3) (coe v25))
                    v26
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v5
        -> case coe v4 of
             C_valid'45'μ'45'wf_890 v11 v13
               -> coe
                    C_valid'45'μ'45'wf_890 v11
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3662
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v5) (coe v0))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v5) (coe v0))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v11) (coe v1))
                       (coe v2) (coe v3) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v5
        -> case coe v4 of
             C_valid'45'ν'45'wf_906 v11 v13
               -> coe
                    C_valid'45'ν'45'wf_906 v11
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3662
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v5) (coe v0))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v5) (coe v0))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v11) (coe v1))
                       (coe v2) (coe v3) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v4 of
             C_valid'45'int'45'wf_918 v10
               -> coe C_valid'45'int'45'wf_918 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v4 of
             C_valid'45'float'45'wf_930 v10
               -> coe C_valid'45'float'45'wf_930 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v4 of
             C_valid'45'str'45'wf_942 v10
               -> coe C_valid'45'str'45'wf_942 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v4 of
             C_valid'45'buffer'45'wf_954 v10
               -> coe C_valid'45'buffer'45'wf_954 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_3934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'mem'45'preserved_3934 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8
                                      v9 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'preserved_3934
      v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'preserved_3934 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'mem'45'preserved_3934 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_778))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_804 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_4000 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_4002 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_854 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_4096 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_874 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_4140 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_834 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_4052 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_890 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_890 v15
                    (coe
                       du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_906 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_906 v15
                    (coe
                       du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) (coe v5))
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_918 v14 -> coe C_valid'45'int'45'wf_918 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_930 v14
               -> coe C_valid'45'float'45'wf_930 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_942 v14 -> coe C_valid'45'str'45'wf_942 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_954 v14
               -> coe C_valid'45'buffer'45'wf_954 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_3996 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_3996 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_3998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_3998 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_fv''_4000 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24 ~v25
  = du_fv''_4000 v0 v1 v2 v4 v5 v7 v10 v11 v14 v16 v21 v24
du_fv''_4000 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_fv''_4000 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542 -> T_ValidAtWF_542
d_sv''_4002 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 v25
  = du_sv''_4002 v0 v1 v2 v4 v6 v8 v10 v11 v15 v17 v22 v25
du_sv''_4002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_sv''_4002 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_4048 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_4048 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_4050 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_4050 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_BodyCorrect_768 -> T_ValidAtWF_542
d_ev''_4052 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            v14 ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 v24 ~v25
  = du_ev''_4052 v0 v1 v2 v4 v8 v9 v12 v14 v16 v17 v22 v24
du_ev''_4052 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_ev''_4052 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4092 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_4092 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4094 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4094 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_4096 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_4096 v0 v1 v2 v4 v5 v8 v9 v12 v13 v14 v18 v20
du_pv''_4096 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_4096 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny
d_tg''_4136 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4138 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4138 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_pv''_4140 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_4140 v0 v1 v2 v4 v6 v8 v9 v12 v13 v14 v18 v20
du_pv''_4140 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_pv''_4140 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_4278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'mem'45'preserved'45'excluding_4278 ~v0 ~v1 ~v2 ~v3
                                                   ~v4
  = du_validityWF'45'mem'45'preserved'45'excluding_4278
du_validityWF'45'mem'45'preserved'45'excluding_4278 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'mem'45'preserved'45'excluding_4278
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocInRegions
d_LocInRegions_4286 a0 a1 a2 a3 a4 a5 a6 = ()
data T_LocInRegions_4286
  = C_loc'45'in'45'input_4296 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'fresh_4300 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'anc_4306 AgdaAny | C_loc'45'in'45'heap_4310
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_4328 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> Integer -> T_ValidAtWF_542 -> ()
d_LocsInRegions_4328 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_4498 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
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
  T_LocInRegions_4286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_4498 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_4570
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\956-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_4592
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\957-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624 v0
                                                                 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18
                                                                 v19 v20
  = du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v19 v20
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                  v12 v13 v14 v15
  = case coe v14 of
      C_valid'45'unit'45'wf_778 -> coe C_valid'45'unit'45'wf_778
      C_valid'45'pair'45'wf_804 v23 v24 v26 v27 v28 v31 v32 v33 v34 v35
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
                                                C_valid'45'pair'45'wf_804 v23 v24 v26 v27 v28 v31
                                                v32 v33
                                                (coe
                                                   du_fv''_4710 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v36) (coe v38) (coe v23) (coe v26)
                                                   (coe v31) (coe v34) (coe v44))
                                                (coe
                                                   du_sv''_4712 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v37) (coe v39) (coe v24) (coe v27)
                                                   (coe v32) (coe v35) (coe v45))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_834 v17 v20 v21 v23 v25 v27 v28 v29 v32 v33 v34 v35
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
               -> case coe v37 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                      -> coe
                           C_valid'45'closure'45'wf_834 v17 v20 v21 v23 v25 v27 v28 v29 v32
                           v33
                           (coe
                              du_ev''_4784 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8) (coe v9)
                              (coe v10) (coe v11) (coe v12) (coe v13) (coe v17) (coe v21)
                              (coe v25) (coe v27) (coe v32) (coe v34) (coe v39))
                           v35
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'wf_854 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inl'45'wf_854 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_4844 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v31) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_874 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inr'45'wf_874 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_4904 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v32) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'μ'45'wf_890 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v24
               -> coe
                    C_valid'45'μ'45'wf_890 v21
                    (coe
                       d_μ'45'validity'45'in'45'regions'45'stub_4570 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'ν'45'wf_906 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v24
               -> coe
                    C_valid'45'ν'45'wf_906 v21
                    (coe
                       d_ν'45'validity'45'in'45'regions'45'stub_4592 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_918 v21 -> coe C_valid'45'int'45'wf_918 v21
      C_valid'45'float'45'wf_930 v21
        -> coe C_valid'45'float'45'wf_930 v21
      C_valid'45'str'45'wf_942 v21 -> coe C_valid'45'str'45'wf_942 v21
      C_valid'45'buffer'45'wf_954 v21
        -> coe C_valid'45'buffer'45'wf_954 v21
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pl-eq
d_pl'45'eq_4702 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'eq_4702 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.spl-eq
d_spl'45'eq_4704 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_spl'45'eq_4704 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_4706 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_4706 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_4708 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_4708 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 -> AgdaAny -> AgdaAny -> T_ValidAtWF_542
d_fv''_4710 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 v23 ~v24 ~v25 ~v26 ~v27 v28
            ~v29 ~v30 v31 ~v32 ~v33 ~v34 v35 ~v36
  = du_fv''_4710
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v21 v23 v28 v31 v35
du_fv''_4710 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
du_fv''_4710 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 -> AgdaAny -> AgdaAny -> T_ValidAtWF_542
d_sv''_4712 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 v22 ~v23 v24 ~v25 ~v26 ~v27 ~v28
            v29 ~v30 ~v31 v32 ~v33 ~v34 ~v35 v36
  = du_sv''_4712
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v20 v22 v24 v29 v32 v36
du_sv''_4712 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
du_sv''_4712 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cl-eq
d_cl'45'eq_4776 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cl'45'eq_4776 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.scl-eq
d_scl'45'eq_4778 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scl'45'eq_4778 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_4780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_4780 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_4782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_4782 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_BodyCorrect_768 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 -> AgdaAny -> T_ValidAtWF_542
d_ev''_4784 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 ~v19 ~v20 v21 ~v22 v23 v24 ~v25 ~v26 ~v27 ~v28
            v29 ~v30 v31 ~v32 ~v33 ~v34 v35
  = du_ev''_4784
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v21 v23 v24 v29 v31 v35
du_ev''_4784 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
du_ev''_4784 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4838 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 -> T_LocInRegions_4286 -> AgdaAny -> AgdaAny
d_tg''_4838 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_4840 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_4840 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4842 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 -> AgdaAny -> T_ValidAtWF_542
d_pv''_4844 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_4844
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v20 v21 v25 v27 v30
du_pv''_4844 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
du_pv''_4844 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4898 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 -> T_LocInRegions_4286 -> AgdaAny -> AgdaAny
d_tg''_4898 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_4900 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_4900 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4902 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4902 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 ->
  T_LocInRegions_4286 ->
  T_LocInRegions_4286 -> AgdaAny -> T_ValidAtWF_542
d_pv''_4904 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_4904
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v19 v20 v21 v25 v27 v30
du_pv''_4904 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny -> T_ValidAtWF_542
du_pv''_4904 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4624
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_5062 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'mem'45'preserved'45'in'45'regions_5062 ~v0 ~v1 ~v2
                                                       ~v3 ~v4
  = du_validityWF'45'mem'45'preserved'45'in'45'regions_5062
du_validityWF'45'mem'45'preserved'45'in'45'regions_5062 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
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
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'mem'45'preserved'45'in'45'regions_5062
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_5068 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_reclaim'45'alloc_5068 ~v0 ~v1 ~v2 v3 v4
  = du_reclaim'45'alloc_5068 v3 v4
du_reclaim'45'alloc_5068 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_reclaim'45'alloc_5068 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_5082 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_reclaim'45'preserves'45'frontier_5082 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                        v7
  = du_reclaim'45'preserves'45'frontier_5082 v5 v6 v7
du_reclaim'45'preserves'45'frontier_5082 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_reclaim'45'preserves'45'frontier_5082 v0 v1 v2
  = coe
      du_stack'45'alloc'45'advances''_5106 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.stack-alloc-advances'
d_stack'45'alloc'45'advances''_5106 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_stack'45'alloc'45'advances''_5106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10 v11 v12
  = du_stack'45'alloc'45'advances''_5106 v10 v11 v12
du_stack'45'alloc'45'advances''_5106 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_stack'45'alloc'45'advances''_5106 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_654 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_654
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v8) (coe v0))
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_664 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_664 v7
                    v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668 v5
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_5166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
d_validityWF'45'reclaim_5166 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             ~v11 v12
  = du_validityWF'45'reclaim_5166 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v12
du_validityWF'45'reclaim_5166 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'reclaim_5166 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'frontier'45'advance_3300 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v3)))
      (coe du_reclaim'45'alloc_5068 (coe v3) (coe v8)) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v9)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v3)))
      (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_5200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_5200 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.k<start
d_k'60'start_5228 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'start_5228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 v13
  = du_k'60'start_5228 v12 v13
du_k'60'start_5228 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'start_5228 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_5272 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_5272 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_5306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  T_ValidAtWF_542 -> AgdaAny -> AgdaAny -> T_ValidAtWF_542
d_validityWF'45'trace'45'preserves_5306 v0 v1 v2 ~v3 v4 v5 v6 v7
                                        ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_validityWF'45'trace'45'preserves_5306
      v0 v1 v2 v4 v5 v6 v7 v9 v11
du_validityWF'45'trace'45'preserves_5306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_542 -> T_ValidAtWF_542
du_validityWF'45'trace'45'preserves_5306 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validityWF'45'mem'45'preserved_3934 (coe v0) (coe v1) (coe v2)
      (coe v4) (coe v3) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2872 (coe v1)
            (coe v5) (coe v7) (coe v4)))
      (coe v8)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_5344 ::
  T_IRResultAWF_698 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_5344 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_5356 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_5356 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_5388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
d_before'45'frontier'45'monotone_5388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7 v8 v9
  = du_before'45'frontier'45'monotone_5388 v7 v8 v9
du_before'45'frontier'45'monotone_5388 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646
du_before'45'frontier'45'monotone_5388 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_654 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_654
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v6) (coe v0))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_664 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_664 v5
             v6 v7 v8
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668 v4
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_668
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_5470 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'compose_5470 = erased
