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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_ir'45'to'45'trace'45'at'45'frontier_12 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'at'45'frontier_740
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
         MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_154 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump
d_AllocBump_32 a0 a1 a2 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.BeforeFrontier
d_BeforeFrontier_36 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.apply-bump
d_apply'45'bump_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_40 ~v0 ~v1 ~v2 = du_apply'45'bump_40
du_apply'45'bump_40 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_40
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_930
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_82 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 -> Integer
d_next'45'heap'45'ref'45'delta_82 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_926
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_84 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 -> Integer
d_next'45'slot'45'delta_84 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_924
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
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_638
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
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_write'45'loc_328
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.exec-trace
d_exec'45'trace_208 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_208 ~v0 v1 ~v2 = du_exec'45'trace_208 v1
du_exec'45'trace_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_208 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2808 (coe v0)
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
d_SumTag_500 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_500 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_524 ::
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
d_transport'45'SumTag_524 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.prim-sv
d_prim'45'sv_536 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv_536 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_prim'45'sv_536 v4 v5
du_prim'45'sv_536 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv_536 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_512
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Int_136)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe v1)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_514
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Float_138)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_200) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_544 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ValidAtWF_544
  = C_valid'45'unit'45'wf_780 |
    C_valid'45'pair'45'wf_806 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.IR.T_AllocMode_4
                              MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                              T_ValidAtWF_544 T_ValidAtWF_544 |
    C_valid'45'closure'45'wf_836 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                                 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                 MAlonzo.Code.Once.IR.T_AllocMode_4
                                 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                                 T_ValidAtWF_544 T_BodyCorrect_770 |
    C_valid'45'inl'45'wf_856 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                             T_ValidAtWF_544 |
    C_valid'45'inr'45'wf_876 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                             T_ValidAtWF_544 |
    C_valid'45'μ'45'wf_892 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                           T_ValidAtWF_544 |
    C_valid'45'ν'45'wf_908 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                           T_ValidAtWF_544 |
    C_valid'45'int'45'wf_920 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 |
    C_valid'45'float'45'wf_932 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 |
    C_valid'45'str'45'wf_944 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 |
    C_valid'45'buffer'45'wf_956 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_560 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ValidAtWF_544
d_valid'45'primitive'45'wf_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9 v10 ~v11
  = du_valid'45'primitive'45'wf_560 v9 v10
du_valid'45'primitive'45'wf_560 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544
du_valid'45'primitive'45'wf_560 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_512
        -> coe C_valid'45'int'45'wf_920 v1
      MAlonzo.Code.Once.IRTy.C_fits'45'float_514
        -> coe C_valid'45'float'45'wf_932 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ResultPlace
d_ResultPlace_574 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ResultPlace_574
  = C_unit'45'result_974 |
    C_at'45'loc_990 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                    T_ValidAtWF_544
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                    T_ValidAtWF_544
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 |
    C_at'45'reg_1008 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                     MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                     MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-loc
d_place'45'loc_588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_place'45'loc_588 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_place'45'loc_588 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_place'45'loc_588 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_place'45'loc_588 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_974
        -> coe
             seq (coe v3)
             (coe d_unit'45'result'45'loc'45'stub_1018 v0 v1 v2 v4 v5 v6 v7)
      C_at'45'loc_990 v15 v16 v17 v19 v20 -> coe v15
      C_at'45'reg_1008 v15 v16 v17 v19 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-before
d_place'45'before_604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_place'45'before_604 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_place'45'before_604 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_place'45'before_604 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_place'45'before_604 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_974
        -> coe
             seq (coe v3) (coe d_before'45'stub_1030 v0 v1 v2 v4 v5 v6 v7)
      C_at'45'loc_990 v15 v16 v17 v19 v20 -> coe v17
      C_at'45'reg_1008 v15 v16 v17 v19 -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-sv
d_place'45'sv_618 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_place'45'sv_618 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_unit'45'result_974
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70
                (coe d_unit'45'result'45'sv'45'loc_1042 v0 v1 v2 v4 v5 v6 v8))
      C_at'45'loc_990 v16 v17 v18 v20 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v16)
      C_at'45'reg_1008 v16 v17 v18 v20
        -> coe du_prim'45'sv_536 (coe v17) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-rax
d_place'45'rax_634 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_634 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-cont-before
d_place'45'cont'45'before_650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_place'45'cont'45'before_650 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_place'45'cont'45'before_650 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_place'45'cont'45'before_650 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_place'45'cont'45'before_650 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_974
        -> coe seq (coe v3) (coe d_before'45'cs_1066 v0 v1 v2 v4 v5 v6 v7)
      C_at'45'loc_990 v15 v16 v17 v19 v20 -> coe v20
      C_at'45'reg_1008 v15 v16 v17 v19 -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase
d_IRResultBase_666 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultBase_666
  = C_constructor_1146 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918
                       T_ResultPlace_574
                       MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 AgdaAny
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_676 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IRStackBudget_676
  = C_constructor_1218 Integer Integer
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
d_IRHeapBudget_684 a0 a1 a2 a3 a4 a5 = ()
data T_IRHeapBudget_684
  = C_constructor_1248 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_700 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IRResultAWF_700
  = C_constructor_1350 T_IRResultBase_666 T_IRStackBudget_676
                       T_IRHeapBudget_684
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_754 ::
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  T_IRStackBudget_676 -> T_IRHeapBudget_684 -> T_IRResultAWF_700
d_mk'45'IRResultAWF'45'via'45'bump_754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 v10 ~v11 v12 v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19
                                       ~v20 v21 ~v22 v23 v24 v25
  = du_mk'45'IRResultAWF'45'via'45'bump_754
      v10 v12 v13 v18 v21 v23 v24 v25
du_mk'45'IRResultAWF'45'via'45'bump_754 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  T_ResultPlace_574 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  AgdaAny ->
  T_IRStackBudget_676 -> T_IRHeapBudget_684 -> T_IRResultAWF_700
du_mk'45'IRResultAWF'45'via'45'bump_754 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1350 (coe C_constructor_1146 v0 v1 v2 v3 v4 v5)
      (coe v6) (coe v7)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_770 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_BodyCorrect_770
  = C_constructor_1450 Integer
                       (AgdaAny ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        T_ValidAtWF_544 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-loc-stub
d_unit'45'result'45'loc'45'stub_1018
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-loc-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-stub
d_before'45'stub_1030
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc
d_unit'45'result'45'sv'45'loc_1042
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub
d_rax'45'stub_1054
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-cs
d_before'45'cs_1066
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-cs"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_1112 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_1112 v0
  = case coe v0 of
      C_constructor_1146 v1 v2 v3 v7 v10 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace
d_trace_1114 ::
  T_IRResultBase_666 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_trace_1114 v0
  = case coe v0 of
      C_constructor_1146 v1 v2 v3 v7 v10 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.bump
d_bump_1116 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918
d_bump_1116 v0
  = case coe v0 of
      C_constructor_1146 v1 v2 v3 v7 v10 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1118 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1118 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_1120 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1120 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_1122 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1122 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_1124 :: T_IRResultBase_666 -> T_ResultPlace_574
d_result'45'place_1124 v0
  = case coe v0 of
      C_constructor_1146 v1 v2 v3 v7 v10 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_1126 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1126 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_1130 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1130 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_1132 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230
d_trace'45'twf_1132 v0
  = case coe v0 of
      C_constructor_1146 v1 v2 v3 v7 v10 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_1138 ::
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1138 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1140 :: T_IRResultBase_666 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1140 v0
  = case coe v0 of
      C_constructor_1146 v1 v2 v3 v7 v10 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_1142 ::
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
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_1142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1142 v9 v10
du_final'45'alloc_1142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultBase_666 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_1142 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_930
      (coe d_bump_1116 (coe v1)) (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_1144 ::
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
  T_IRResultBase_666 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1144 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_1184 :: T_IRStackBudget_676 -> Integer
d_max'45'slot'45'written_1184 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_1186 :: T_IRStackBudget_676 -> Integer
d_stack'45'budget_1186 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1188 ::
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1188 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1190 ::
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1190 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1192 ::
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1192 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_1198 ::
  T_IRStackBudget_676 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1198 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_1200 :: T_IRStackBudget_676 -> AgdaAny
d_trace'45'writes'45'above_1200 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1202 ::
  T_IRStackBudget_676 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1202 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_1204 :: T_IRStackBudget_676 -> AgdaAny
d_trace'45'writes'45'below_1204 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1206 ::
  T_IRStackBudget_676 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1206 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_1208 :: T_IRStackBudget_676 -> Integer
d_scratch'45'budget_1208 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_1210 ::
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1210 v0
  = case coe v0 of
      C_constructor_1218 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_1212 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1212 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_slot'45'monotone_1212 v3
du_slot'45'monotone_1212 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1212 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1214 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1214 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7
  = du_slot'45'stays'45'in'45'budget_1214 v3 v4 v7
du_slot'45'stays'45'in'45'budget_1214 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  T_IRStackBudget_676 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1214 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_924
         (coe v1))
      (d_stack'45'budget_1186 (coe v2))
      (d_bump'45'fits'45'stack'45'budget_1188 (coe v2))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_1236 :: T_IRHeapBudget_684 -> Integer
d_heap'45'budget_1236 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1238 ::
  T_IRHeapBudget_684 -> Integer
d_max'45'heap'45'ref'45'written_1238 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1240 ::
  T_IRHeapBudget_684 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1240 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1242 ::
  T_IRHeapBudget_684 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1242 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1244 ::
  T_IRHeapBudget_684 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1244 v0
  = case coe v0 of
      C_constructor_1248 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_1246 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_IRHeapBudget_684 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1246 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_heap'45'monotone_1246 v3
du_heap'45'monotone_1246 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1246 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.base
d_base_1270 :: T_IRResultAWF_700 -> T_IRResultBase_666
d_base_1270 v0
  = case coe v0 of
      C_constructor_1350 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_1272 :: T_IRResultAWF_700 -> T_IRStackBudget_676
d_stack'45'inv_1272 v0
  = case coe v0 of
      C_constructor_1350 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_1274 :: T_IRResultAWF_700 -> T_IRHeapBudget_684
d_heap'45'inv_1274 v0
  = case coe v0 of
      C_constructor_1350 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.alloc-correct
d_alloc'45'correct_1278 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1278 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump
d_bump_1280 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_918
d_bump_1280 v0 = coe d_bump_1116 (coe d_base_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-alloc
d_final'45'alloc_1282 ::
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
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_final'45'alloc_1282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_final'45'alloc_1282 v9 v10
du_final'45'alloc_1282 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_final'45'alloc_1282 v0 v1
  = coe du_final'45'alloc_1142 (coe v0) (coe d_base_1270 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-state
d_final'45'state_1284 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_final'45'state_1284 v0
  = coe d_final'45'state_1112 (coe d_base_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frame-preserved
d_frame'45'preserved_1286 ::
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
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1286 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.mem-preserved-before
d_mem'45'preserved'45'before_1288 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1288 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.not-halted
d_not'45'halted_1290 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1290 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.result-place
d_result'45'place_1292 :: T_IRResultAWF_700 -> T_ResultPlace_574
d_result'45'place_1292 v0
  = coe d_result'45'place_1124 (coe d_base_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace
d_trace_1294 ::
  T_IRResultAWF_700 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212]
d_trace_1294 v0 = coe d_trace_1114 (coe d_base_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-correct
d_trace'45'correct_1296 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1296 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1298 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1298 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1300 :: T_IRResultAWF_700 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1300 v0
  = coe d_trace'45'no'45'frame'45'ops_1140 (coe d_base_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-preserves-halted
d_trace'45'preserves'45'halted_1302 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1302 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-twf
d_trace'45'twf_1304 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8230
d_trace'45'twf_1304 v0
  = coe d_trace'45'twf_1132 (coe d_base_1270 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1308 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1308 v0
  = coe
      d_bump'45'fits'45'stack'45'budget_1188
      (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frontier-slot-stable
d_frontier'45'slot'45'stable_1310 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1310 v0
  = coe
      d_frontier'45'slot'45'stable_1198
      (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1312 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1312 v0
  = coe
      d_max'45'slot'45'geq'45'final_1190
      (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1314 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1314 v0
  = coe
      d_max'45'slot'45'usage'45'bound_1192
      (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-written
d_max'45'slot'45'written_1316 :: T_IRResultAWF_700 -> Integer
d_max'45'slot'45'written_1316 v0
  = coe
      d_max'45'slot'45'written_1184 (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-bounded
d_scratch'45'bounded_1318 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1318 v0
  = coe d_scratch'45'bounded_1210 (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-budget
d_scratch'45'budget_1320 :: T_IRResultAWF_700 -> Integer
d_scratch'45'budget_1320 v0
  = coe d_scratch'45'budget_1208 (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-monotone
d_slot'45'monotone_1322 ::
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
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_slot'45'monotone_1322 v9
du_slot'45'monotone_1322 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1322 v0 = coe du_slot'45'monotone_1212 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1324 ::
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
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 v9 v10
  = du_slot'45'stays'45'in'45'budget_1324 v9 v10
du_slot'45'stays'45'in'45'budget_1324 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1324 v0 v1
  = coe
      du_slot'45'stays'45'in'45'budget_1214 (coe v0)
      (coe d_bump_1116 (coe d_base_1270 (coe v1)))
      (coe d_stack'45'inv_1272 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.stack-budget
d_stack'45'budget_1326 :: T_IRResultAWF_700 -> Integer
d_stack'45'budget_1326 v0
  = coe d_stack'45'budget_1186 (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1328 ::
  T_IRResultAWF_700 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1328 v0
  = coe
      d_trace'45'slot'45'reads'45'above_1202
      (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1330 ::
  T_IRResultAWF_700 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1330 v0
  = coe
      d_trace'45'slot'45'reads'45'below_1206
      (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-above
d_trace'45'writes'45'above_1332 :: T_IRResultAWF_700 -> AgdaAny
d_trace'45'writes'45'above_1332 v0
  = coe
      d_trace'45'writes'45'above_1200 (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-below
d_trace'45'writes'45'below_1334 :: T_IRResultAWF_700 -> AgdaAny
d_trace'45'writes'45'below_1334 v0
  = coe
      d_trace'45'writes'45'below_1204 (coe d_stack'45'inv_1272 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1338 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1338 v0
  = coe
      d_bump'45'fits'45'heap'45'budget_1240
      (coe d_heap'45'inv_1274 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-budget
d_heap'45'budget_1340 :: T_IRResultAWF_700 -> Integer
d_heap'45'budget_1340 v0
  = coe d_heap'45'budget_1236 (coe d_heap'45'inv_1274 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-monotone
d_heap'45'monotone_1342 ::
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
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_heap'45'monotone_1342 v9
du_heap'45'monotone_1342 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1342 v0 = coe du_heap'45'monotone_1246 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1344 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1344 v0
  = coe
      d_max'45'heap'45'ref'45'geq'45'final_1242
      (coe d_heap'45'inv_1274 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1346 ::
  T_IRResultAWF_700 -> Integer
d_max'45'heap'45'ref'45'written_1346 v0
  = coe
      d_max'45'heap'45'ref'45'written_1238
      (coe d_heap'45'inv_1274 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1348 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1348 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1244
      (coe d_heap'45'inv_1274 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_1430 :: T_BodyCorrect_770 -> Integer
d_body'45'capacity_1430 v0
  = case coe v0 of
      C_constructor_1450 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_1432 ::
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_1432 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.execute
d_execute_1448 ::
  T_BodyCorrect_770 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_1448 v0
  = case coe v0 of
      C_constructor_1450 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_1468 ::
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
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_1468 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-via-budget
d_bound'45'via'45'budget_1480 ::
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
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'via'45'budget_1480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 v10 ~v11
  = du_bound'45'via'45'budget_1480 v10
du_bound'45'via'45'budget_1480 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'via'45'budget_1480 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1244
      (coe d_heap'45'inv_1274 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-alloc
d_bound'45'alloc_1484 ::
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
  T_IRResultAWF_700 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'alloc_1484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      ~v11
  = du_bound'45'alloc_1484 v10
du_bound'45'alloc_1484 ::
  T_IRResultAWF_700 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'alloc_1484 v0
  = coe du_bound'45'via'45'budget_1480 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_1510 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13
  = ()
data T_ClosureWellFormed_1510
  = C_constructor_1566 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.IR.T_AllocMode_4 T_ValidAtWF_544
                       T_BodyCorrect_770
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_1550 ::
  T_ClosureWellFormed_1510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1550 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_1552 ::
  T_ClosureWellFormed_1510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1552 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_1554 ::
  T_ClosureWellFormed_1510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_env'45'before_1554 v0
  = case coe v0 of
      C_constructor_1566 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_1556 ::
  T_ClosureWellFormed_1510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_code'45'before_1556 v0
  = case coe v0 of
      C_constructor_1566 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_1558 ::
  T_ClosureWellFormed_1510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sucLoc'45'before_1558 v0
  = case coe v0 of
      C_constructor_1566 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_1560 ::
  T_ClosureWellFormed_1510 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1560 v0
  = case coe v0 of
      C_constructor_1566 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_1562 :: T_ClosureWellFormed_1510 -> T_ValidAtWF_544
d_env'45'valid_1562 v0
  = case coe v0 of
      C_constructor_1566 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_1564 ::
  T_ClosureWellFormed_1510 -> T_BodyCorrect_770
d_body'45'correct_1564 v0
  = case coe v0 of
      C_constructor_1566 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_1580 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_ClosureValidWF_1580
  = C_constructor_1654 MAlonzo.Code.Once.IRTy.T_IRTy_6
                       MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       T_ValidAtWF_544 T_BodyCorrect_770
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_1624 ::
  T_ClosureValidWF_1580 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1624 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body
d_body_1626 ::
  T_ClosureValidWF_1580 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1626 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env
d_env_1628 :: T_ClosureValidWF_1580 -> AgdaAny
d_env_1628 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body<bound
d_body'60'bound_1630 ::
  T_ClosureValidWF_1580 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_1630 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-loc
d_env'45'loc_1632 ::
  T_ClosureValidWF_1580 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_1632 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_1634 ::
  T_ClosureValidWF_1580 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_body'45'label_1634 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.mEnv
d_mEnv_1636 ::
  T_ClosureValidWF_1580 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1636 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-ptr
d_env'45'ptr_1638 ::
  T_ClosureValidWF_1580 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1638 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_1640 ::
  T_ClosureValidWF_1580 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1640 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-before
d_env'45'before_1642 ::
  T_ClosureValidWF_1580 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_env'45'before_1642 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1644 ::
  T_ClosureValidWF_1580 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sucLoc'45'before_1644 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-valid
d_env'45'valid_1646 :: T_ClosureValidWF_1580 -> T_ValidAtWF_544
d_env'45'valid_1646 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-correct
d_body'45'correct_1648 ::
  T_ClosureValidWF_1580 -> T_BodyCorrect_770
d_body'45'correct_1648 v0
  = case coe v0 of
      C_constructor_1654 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1652 ::
  T_ClosureValidWF_1580 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1652 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_1670 ::
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
  T_ValidAtWF_544 -> T_ClosureValidWF_1580
d_decomposeClosureWF_1670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10
  = du_decomposeClosureWF_1670 v10
du_decomposeClosureWF_1670 ::
  T_ValidAtWF_544 -> T_ClosureValidWF_1580
du_decomposeClosureWF_1670 v0
  = case coe v0 of
      C_valid'45'closure'45'wf_836 v2 v5 v6 v8 v10 v12 v13 v14 v17 v18 v19 v20
        -> coe C_constructor_1654 v2 v5 v6 v8 v10 v13 v12 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_1700 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> Integer -> ()
d_RecDispatcherWF_1700 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF
d_PairValidWF_1734 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_PairValidWF_1734
  = C_constructor_1792 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       T_ValidAtWF_544 T_ValidAtWF_544
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-loc
d_fst'45'loc_1770 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_1770 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-loc
d_snd'45'loc_1772 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_1772 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mA
d_mA_1774 ::
  T_PairValidWF_1734 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1774 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mB
d_mB_1776 ::
  T_PairValidWF_1734 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1776 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-ptr
d_fst'45'ptr_1778 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_1778 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-ptr
d_snd'45'ptr_1780 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_1780 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-before
d_fst'45'before_1782 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_fst'45'before_1782 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-before
d_snd'45'before_1784 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_snd'45'before_1784 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_1786 ::
  T_PairValidWF_1734 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sucLoc'45'before_1786 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-valid
d_fst'45'valid_1788 :: T_PairValidWF_1734 -> T_ValidAtWF_544
d_fst'45'valid_1788 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-valid
d_snd'45'valid_1790 :: T_PairValidWF_1734 -> T_ValidAtWF_544
d_snd'45'valid_1790 v0
  = case coe v0 of
      C_constructor_1792 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_1808 ::
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
  T_ValidAtWF_544 -> T_PairValidWF_1734
d_decomposePairWF_1808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_decomposePairWF_1808 v10
du_decomposePairWF_1808 :: T_ValidAtWF_544 -> T_PairValidWF_1734
du_decomposePairWF_1808 v0
  = case coe v0 of
      C_valid'45'pair'45'wf_806 v8 v9 v11 v12 v13 v16 v17 v18 v19 v20
        -> coe C_constructor_1792 v8 v9 v11 v12 v16 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF
d_InlValidWF_1846 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InlValidWF_1846
  = C_constructor_1892 AgdaAny MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       T_ValidAtWF_544
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.a
d_a_1876 :: T_InlValidWF_1846 -> AgdaAny
d_a_1876 v0
  = case coe v0 of
      C_constructor_1892 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.mA
d_mA_1878 ::
  T_InlValidWF_1846 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1878 v0
  = case coe v0 of
      C_constructor_1892 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-loc
d_payload'45'loc_1880 ::
  T_InlValidWF_1846 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_1880 v0
  = case coe v0 of
      C_constructor_1892 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-ptr
d_payload'45'ptr_1882 ::
  T_InlValidWF_1846 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_1882 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-before
d_payload'45'before_1884 ::
  T_InlValidWF_1846 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_payload'45'before_1884 v0
  = case coe v0 of
      C_constructor_1892 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_1886 ::
  T_InlValidWF_1846 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sucLoc'45'before_1886 v0
  = case coe v0 of
      C_constructor_1892 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-valid
d_payload'45'valid_1888 :: T_InlValidWF_1846 -> T_ValidAtWF_544
d_payload'45'valid_1888 v0
  = case coe v0 of
      C_constructor_1892 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_1890 ::
  T_InlValidWF_1846 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_1890 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF
d_InrValidWF_1906 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_InrValidWF_1906
  = C_constructor_1952 AgdaAny MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
                       T_ValidAtWF_544
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.b
d_b_1936 :: T_InrValidWF_1906 -> AgdaAny
d_b_1936 v0
  = case coe v0 of
      C_constructor_1952 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.mB
d_mB_1938 ::
  T_InrValidWF_1906 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1938 v0
  = case coe v0 of
      C_constructor_1952 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-loc
d_payload'45'loc_1940 ::
  T_InrValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_1940 v0
  = case coe v0 of
      C_constructor_1952 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-ptr
d_payload'45'ptr_1942 ::
  T_InrValidWF_1906 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_1942 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-before
d_payload'45'before_1944 ::
  T_InrValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_payload'45'before_1944 v0
  = case coe v0 of
      C_constructor_1952 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_1946 ::
  T_InrValidWF_1906 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sucLoc'45'before_1946 v0
  = case coe v0 of
      C_constructor_1952 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-valid
d_payload'45'valid_1948 :: T_InrValidWF_1906 -> T_ValidAtWF_544
d_payload'45'valid_1948 v0
  = case coe v0 of
      C_constructor_1952 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_1950 ::
  T_InrValidWF_1906 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_1950 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_1968 ::
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
  T_ValidAtWF_544 -> T_InlValidWF_1846
d_decomposeInlWF_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInlWF_1968 v7 v10
du_decomposeInlWF_1968 ::
  AgdaAny -> T_ValidAtWF_544 -> T_InlValidWF_1846
du_decomposeInlWF_1968 v0 v1
  = case coe v1 of
      C_valid'45'inl'45'wf_856 v8 v10 v11 v14 v15 v16
        -> coe C_constructor_1892 v0 v10 v8 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_2004 ::
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
  T_ValidAtWF_544 -> T_InrValidWF_1906
d_decomposeInrWF_2004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_decomposeInrWF_2004 v7 v10
du_decomposeInrWF_2004 ::
  AgdaAny -> T_ValidAtWF_544 -> T_InrValidWF_1906
du_decomposeInrWF_2004 v0 v1
  = case coe v1 of
      C_valid'45'inr'45'wf_876 v8 v10 v11 v14 v15 v16
        -> coe C_constructor_1952 v0 v10 v8 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_2034 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_544
d_valid'45'to'45'validWF'45'unit_2034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_valid'45'to'45'validWF'45'unit_2034
du_valid'45'to'45'validWF'45'unit_2034 :: T_ValidAtWF_544
du_valid'45'to'45'validWF'45'unit_2034
  = coe C_valid'45'unit'45'wf_780
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_2050 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'mem'45'only_2050 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 v9
                                 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'only_2050 v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'only_2050 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'mem'45'only_2050 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_780))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v31))
                           (coe
                              du_sv''_2118 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2256 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2168 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_892 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_892 v15
                    (coe
                       du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_908 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_908 v15
                    (coe
                       du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_920 v14 -> coe C_valid'45'int'45'wf_920 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_932 v14
               -> coe C_valid'45'float'45'wf_932 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_944 v14 -> coe C_valid'45'str'45'wf_944 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_956 v14
               -> coe C_valid'45'buffer'45'wf_956 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2112 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2112 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2114 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2114 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2116 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_fv''_2116 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_fv''_2116 v0 v1 v2 v4 v5 v7 v10 v11 v14 v16 v24
du_fv''_2116 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_fv''_2116 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2118 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_sv''_2118 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_sv''_2118 v0 v1 v2 v4 v6 v8 v10 v11 v15 v17 v25
du_sv''_2118 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_sv''_2118 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2164 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2164 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2166 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2166 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2168 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_BodyCorrect_770 -> T_ValidAtWF_544
d_ev''_2168 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            v14 ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_ev''_2168 v0 v1 v2 v4 v8 v9 v12 v14 v16 v17 v24
du_ev''_2168 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_ev''_2168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2208 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_2208 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2210 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2210 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2212 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_2212 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2212 v0 v1 v2 v4 v5 v8 v9 v12 v13 v14 v20
du_pv''_2212 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_2212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2252 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_2252 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2254 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2254 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2256 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_2256 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_2256 v0 v1 v2 v4 v6 v8 v9 v12 v13 v14 v20
du_pv''_2256 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_2256 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'only_2050 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_2384 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'write'45'at'45'frontier_2384 v0 v1 v2 ~v3 v4 v5 v6
                                             ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'frontier_2384
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'frontier_2384 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'write'45'at'45'frontier_2384 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_780)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2446 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_2448 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2538 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2580 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_892 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_892 v15
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_908 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_908 v15
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_920 v14 -> coe C_valid'45'int'45'wf_920 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_932 v14
               -> coe C_valid'45'float'45'wf_932 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_944 v14 -> coe C_valid'45'str'45'wf_944 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_956 v14
               -> coe C_valid'45'buffer'45'wf_956 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2442 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2442 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2444 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2444 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2446 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_fv''_2446 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2446 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_2446 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_fv''_2446 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2448 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_sv''_2448 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_2448 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_2448 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_sv''_2448 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2492 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2492 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2494 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2494 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2496 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_BodyCorrect_770 -> T_ValidAtWF_544
d_ev''_2496 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_2496 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_2496 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_ev''_2496 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2534 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_2534 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2536 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2536 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2538 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_2538 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2538 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_2538 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_2538 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2576 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_2576 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2578 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2578 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2580 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_2580 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2580 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_2580 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_2580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'frontier_2384 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_2696 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'write'45'at'45'suc'45'frontier_2696 v0 v1 v2 ~v3 v4
                                                    v5 v6 ~v7 v8 v9 ~v10 v11
  = du_validityWF'45'write'45'at'45'suc'45'frontier_2696
      v0 v1 v2 v4 v5 v6 v8 v9 v11
du_validityWF'45'write'45'at'45'suc'45'frontier_2696 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'write'45'at'45'suc'45'frontier_2696 v0 v1 v2 v3 v4
                                                     v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v8) (coe C_valid'45'unit'45'wf_780)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_2758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_2760 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_2892 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_2808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_892 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_892 v15
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_908 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_908 v15
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
                       (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_920 v14 -> coe C_valid'45'int'45'wf_920 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_932 v14
               -> coe C_valid'45'float'45'wf_932 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_944 v14 -> coe C_valid'45'str'45'wf_944 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_956 v14
               -> coe C_valid'45'buffer'45'wf_956 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2754 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2754 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2756 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2756 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2758 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_fv''_2758 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2758 v0 v1 v2 v4 v5 v7 v10 v11 v13 v15 v20 v23
du_fv''_2758 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_fv''_2758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2760 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_sv''_2760 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_2760 v0 v1 v2 v4 v6 v8 v10 v11 v14 v16 v21 v24
du_sv''_2760 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_sv''_2760 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2804 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2804 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2806 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2806 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2808 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_BodyCorrect_770 -> T_ValidAtWF_544
d_ev''_2808 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_2808 v0 v1 v2 v4 v8 v9 v11 v13 v15 v16 v21 v23
du_ev''_2808 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_ev''_2808 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v7) (coe v4) (coe v5)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2846 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_2846 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2848 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2848 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2850 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_2850 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2850 v0 v1 v2 v4 v5 v8 v9 v11 v12 v13 v17 v19
du_pv''_2850 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_2850 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2888 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_2888 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2890 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2890 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2892 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_2892 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_2892 v0 v1 v2 v4 v6 v8 v9 v11 v12 v13 v17 v19
du_pv''_2892 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_2892 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2696 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v7) (coe v5) (coe v6)
      (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_3010 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'alloc'45'advance_3010 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
                                      v9 v10
  = du_validityWF'45'alloc'45'advance_3010
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v10
du_validityWF'45'alloc'45'advance_3010 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Integer -> T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'alloc'45'advance_3010 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v9) (coe C_valid'45'unit'45'wf_780))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> case coe v9 of
                    C_valid'45'pair'45'wf_806 v21 v22 v24 v25 v26 v29 v30 v31 v32 v33
                      -> coe
                           C_valid'45'pair'45'wf_806 v21 v22 v24 v25 v26
                           (coe du_fb''_3064 (coe v3) (coe v21) (coe v29))
                           (coe du_sb''_3066 (coe v3) (coe v22) (coe v30))
                           (coe du_slb''_3068 (coe v3) (coe v6) (coe v31))
                           (coe
                              du_fv''_3070 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v7) (coe v8) (coe v21) (coe v24) (coe v32))
                           (coe
                              du_sv''_3072 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                              (coe v13) (coe v7) (coe v8) (coe v22) (coe v25) (coe v33))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
        -> case coe v9 of
             C_valid'45'inl'45'wf_856 v18 v20 v21 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v27
                      -> coe
                           C_valid'45'inl'45'wf_856 v18 v20 v21
                           (coe du_pb''_3154 (coe v3) (coe v18) (coe v24))
                           (coe du_slb''_3156 (coe v3) (coe v6) (coe v25))
                           (coe
                              du_pv''_3158 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v7)
                              (coe v8) (coe v27) (coe v18) (coe v20) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v18 v20 v21 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v27
                      -> coe
                           C_valid'45'inr'45'wf_876 v18 v20 v21
                           (coe du_pb''_3194 (coe v3) (coe v18) (coe v24))
                           (coe du_slb''_3196 (coe v3) (coe v6) (coe v25))
                           (coe
                              du_pv''_3198 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v7)
                              (coe v8) (coe v27) (coe v18) (coe v20) (coe v26))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
        -> case coe v9 of
             C_valid'45'closure'45'wf_836 v13 v16 v17 v19 v21 v23 v24 v25 v28 v29 v30 v31
               -> coe
                    C_valid'45'closure'45'wf_836 v13 v16 v17 v19 v21 v23 v24 v25
                    (coe du_eb''_3114 (coe v3) (coe v21) (coe v28))
                    (coe du_slb''_3116 (coe v3) (coe v6) (coe v29))
                    (coe
                       du_ev''_3118 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                       (coe v13) (coe v17) (coe v21) (coe v23) (coe v30))
                    v31
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
        -> case coe v9 of
             C_valid'45'μ'45'wf_892 v16 v18
               -> coe
                    C_valid'45'μ'45'wf_892 v16
                    (coe
                       du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v16) v5)
                       (coe v6) (coe v7) (coe v8) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
        -> case coe v9 of
             C_valid'45'ν'45'wf_908 v16 v18
               -> coe
                    C_valid'45'ν'45'wf_908 v16
                    (coe
                       du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v16) v5)
                       (coe v6) (coe v7) (coe v8) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v9 of
             C_valid'45'int'45'wf_920 v15
               -> coe
                    C_valid'45'int'45'wf_920
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v9 of
             C_valid'45'float'45'wf_932 v15
               -> coe
                    C_valid'45'float'45'wf_932
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v9 of
             C_valid'45'str'45'wf_944 v15
               -> coe
                    C_valid'45'str'45'wf_944
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v9 of
             C_valid'45'buffer'45'wf_956 v15
               -> coe
                    C_valid'45'buffer'45'wf_956
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
                       (coe v3) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_3064 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_fb''_3064 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22 ~v23
  = du_fb''_3064 v4 v12 v19
du_fb''_3064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_fb''_3064 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_3066 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sb''_3066 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_sb''_3066 v4 v13 v20
du_sb''_3066 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_sb''_3066 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3068 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3068 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_slb''_3068 v4 v9 v21
du_slb''_3068 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3068 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3070 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_fv''_3070 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_fv''_3070 v0 v1 v2 v4 v5 v7 v10 v11 v12 v14 v22
du_fv''_3070 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_fv''_3070 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v8) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3072 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_sv''_3072 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 v13 ~v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23
  = du_sv''_3072 v0 v1 v2 v4 v6 v8 v10 v11 v13 v15 v23
du_sv''_3072 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_sv''_3072 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v8) (coe v6) (coe v7) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_3114 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_eb''_3114 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 ~v23
  = du_eb''_3114 v4 v14 v20
du_eb''_3114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_eb''_3114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3116 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3116 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_slb''_3116 v4 v7 v21
du_slb''_3116 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3116 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3118 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_BodyCorrect_770 -> T_ValidAtWF_544
d_ev''_3118 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11 v12 ~v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23
  = du_ev''_3118 v0 v1 v2 v4 v8 v9 v10 v12 v14 v15 v22
du_ev''_3118 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_ev''_3118 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v8) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3154 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_pb''_3154 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_3154 v4 v11 v16
du_pb''_3154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_pb''_3154 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3156 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3156 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_3156 v4 v7 v17
du_slb''_3156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3156 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3158 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_3158 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_3158 v0 v1 v2 v4 v5 v8 v9 v10 v11 v12 v18
du_pv''_3158 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_3158 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v8) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3194 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_pb''_3194 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_pb''_3194 v4 v11 v16
du_pb''_3194 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_pb''_3194 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3196 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3196 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_slb''_3196 v4 v7 v17
du_slb''_3196 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3196 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_786
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3198 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_3198 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18
  = du_pv''_3198 v0 v1 v2 v4 v6 v8 v9 v10 v11 v12 v18
du_pv''_3198 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_3198 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'alloc'45'advance_3010 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v8) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_3302 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'frontier'45'advance_3302 v0 v1 v2 ~v3 v4 v5 v6 v7
                                         v8 v9 ~v10 v11 v12 v13
  = du_validityWF'45'frontier'45'advance_3302
      v0 v1 v2 v4 v5 v6 v7 v8 v9 v11 v12 v13
du_validityWF'45'frontier'45'advance_3302 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'frontier'45'advance_3302 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 v11
  = case coe v5 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v6) (coe seq (coe v11) (coe C_valid'45'unit'45'wf_780))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
               -> case coe v11 of
                    C_valid'45'pair'45'wf_806 v23 v24 v26 v27 v28 v31 v32 v33 v34 v35
                      -> coe
                           C_valid'45'pair'45'wf_806 v23 v24 v26 v27 v28
                           (coe du_fb''_3368 (coe v9) (coe v10) (coe v23) (coe v31))
                           (coe du_sb''_3370 (coe v9) (coe v10) (coe v24) (coe v32))
                           (coe du_slb''_3372 (coe v7) (coe v9) (coe v10) (coe v33))
                           (coe
                              du_fv''_3374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                              (coe v14) (coe v8) (coe v9) (coe v10) (coe v23) (coe v26)
                              (coe v34))
                           (coe
                              du_sv''_3376 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
                              (coe v15) (coe v8) (coe v9) (coe v10) (coe v24) (coe v27)
                              (coe v35))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
        -> case coe v11 of
             C_valid'45'inl'45'wf_856 v20 v22 v23 v26 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v29
                      -> coe
                           C_valid'45'inl'45'wf_856 v20 v22 v23
                           (coe du_pb''_3470 (coe v9) (coe v10) (coe v20) (coe v26))
                           (coe du_slb''_3472 (coe v7) (coe v9) (coe v10) (coe v27))
                           (coe
                              du_pv''_3474 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
                              (coe v8) (coe v9) (coe v10) (coe v29) (coe v20) (coe v22)
                              (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v20 v22 v23 v26 v27 v28
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v29
                      -> coe
                           C_valid'45'inr'45'wf_876 v20 v22 v23
                           (coe du_pb''_3516 (coe v9) (coe v10) (coe v20) (coe v26))
                           (coe du_slb''_3518 (coe v7) (coe v9) (coe v10) (coe v27))
                           (coe
                              du_pv''_3520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13)
                              (coe v8) (coe v9) (coe v10) (coe v29) (coe v20) (coe v22)
                              (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v12 v13
        -> case coe v11 of
             C_valid'45'closure'45'wf_836 v15 v18 v19 v21 v23 v25 v26 v27 v30 v31 v32 v33
               -> coe
                    C_valid'45'closure'45'wf_836 v15 v18 v19 v21 v23 v25 v26 v27
                    (coe du_eb''_3424 (coe v9) (coe v10) (coe v23) (coe v30))
                    (coe du_slb''_3426 (coe v7) (coe v9) (coe v10) (coe v31))
                    (coe
                       du_ev''_3428 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                       (coe v9) (coe v10) (coe v15) (coe v19) (coe v23) (coe v25)
                       (coe v32))
                    v33
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
        -> case coe v11 of
             C_valid'45'μ'45'wf_892 v18 v20
               -> coe
                    C_valid'45'μ'45'wf_892 v18
                    (coe
                       du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                       (coe
                          du_eval_24 v1 v5
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v18) v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
        -> case coe v11 of
             C_valid'45'ν'45'wf_908 v18 v20
               -> coe
                    C_valid'45'ν'45'wf_908 v18
                    (coe
                       du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
                       (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                       (coe
                          du_eval_24 v1 v5
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v12) (coe v5))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v18) v6)
                       (coe v7) (coe v8) (coe v9) (coe v10) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v11 of
             C_valid'45'int'45'wf_920 v17
               -> coe
                    C_valid'45'int'45'wf_920
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v11 of
             C_valid'45'float'45'wf_932 v17
               -> coe
                    C_valid'45'float'45'wf_932
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v11 of
             C_valid'45'str'45'wf_944 v17
               -> coe
                    C_valid'45'str'45'wf_944
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v11 of
             C_valid'45'buffer'45'wf_956 v17
               -> coe
                    C_valid'45'buffer'45'wf_956
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
                       (coe v9) (coe v10) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_3368 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_fb''_3368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26
  = du_fb''_3368 v13 v14 v15 v22
du_fb''_3368 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_fb''_3368 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_3370 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_sb''_3370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25 ~v26
  = du_sb''_3370 v13 v14 v16 v23
du_sb''_3370 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_sb''_3370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3372 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
             v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25 ~v26
  = du_slb''_3372 v10 v13 v14 v24
du_slb''_3372 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3372 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3374 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_fv''_3374 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8 ~v9 ~v10 v11 ~v12 v13 v14
            v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
  = du_fv''_3374 v0 v1 v2 v4 v5 v6 v8 v11 v13 v14 v15 v17 v25
du_fv''_3374 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_fv''_3374 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10) (coe v7)
      (coe v8) (coe v9) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3376 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_sv''_3376 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 ~v12 v13 v14
            ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
  = du_sv''_3376 v0 v1 v2 v4 v5 v7 v9 v11 v13 v14 v16 v18 v26
du_sv''_3376 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_sv''_3376 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10) (coe v7)
      (coe v8) (coe v9) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_3424 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_eb''_3424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25 ~v26
  = du_eb''_3424 v11 v12 v17 v23
du_eb''_3424 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_eb''_3424 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3426 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
             ~v26
  = du_slb''_3426 v8 v11 v12 v24
du_slb''_3426 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3426 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3428 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_BodyCorrect_770 -> T_ValidAtWF_544
d_ev''_3428 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 v12 v13 ~v14
            v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
  = du_ev''_3428 v0 v1 v2 v4 v5 v9 v11 v12 v13 v15 v17 v18 v25
du_ev''_3428 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_ev''_3428 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v10) (coe v5)
      (coe v6) (coe v7) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3470 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_pb''_3470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_3470 v11 v12 v14 v19
du_pb''_3470 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_pb''_3470 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3472 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_3472 v8 v11 v12 v20
du_slb''_3472 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3472 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3474 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_3474 v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_3474 v0 v1 v2 v4 v5 v6 v9 v11 v12 v13 v14 v15 v21
du_pv''_3474 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_3474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v10) (coe v6)
      (coe v7) (coe v8) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3516 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_pb''_3516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            ~v13 v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_pb''_3516 v11 v12 v14 v19
du_pb''_3516 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_pb''_3516 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3518 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_slb''_3518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 v11 v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21
  = du_slb''_3518 v8 v11 v12 v20
du_slb''_3518 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_slb''_3518 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_856
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3520 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_3520 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 v11 v12 v13 v14
            v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21
  = du_pv''_3520 v0 v1 v2 v4 v5 v7 v9 v11 v12 v13 v14 v15 v21
du_pv''_3520 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_3520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v10) (coe v6)
      (coe v7) (coe v8) (coe v12)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_3664 ::
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
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652) ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'with'45'bf'45'transfer_3664 ~v0 v1 ~v2 ~v3 v4 v5 v6
                                            ~v7 ~v8 ~v9 v10 v11
  = du_validityWF'45'with'45'bf'45'transfer_3664 v1 v4 v5 v6 v10 v11
du_validityWF'45'with'45'bf'45'transfer_3664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652) ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'with'45'bf'45'transfer_3664 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v2) (coe seq (coe v5) (coe C_valid'45'unit'45'wf_780))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v5 of
                    C_valid'45'pair'45'wf_806 v17 v18 v20 v21 v22 v25 v26 v27 v28 v29
                      -> coe
                           C_valid'45'pair'45'wf_806 v17 v18 v20 v21 v22 (coe v4 v17 v25)
                           (coe v4 v18 v26)
                           (coe
                              v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                              v27)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0) (coe v6)
                              (coe v8) (coe v17) (coe v4) (coe v28))
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0) (coe v7)
                              (coe v9) (coe v18) (coe v4) (coe v29))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v6 v7
        -> case coe v5 of
             C_valid'45'inl'45'wf_856 v14 v16 v17 v20 v21 v22
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v23
                      -> coe
                           C_valid'45'inl'45'wf_856 v14 v16 v17 (coe v4 v14 v20)
                           (coe
                              v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                              v21)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0) (coe v6)
                              (coe v23) (coe v14) (coe v4) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v14 v16 v17 v20 v21 v22
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v23
                      -> coe
                           C_valid'45'inr'45'wf_876 v14 v16 v17 (coe v4 v14 v20)
                           (coe
                              v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                              v21)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0) (coe v7)
                              (coe v23) (coe v14) (coe v4) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v6 v7
        -> case coe v5 of
             C_valid'45'closure'45'wf_836 v9 v12 v13 v15 v17 v19 v20 v21 v24 v25 v26 v27
               -> coe
                    C_valid'45'closure'45'wf_836 v9 v12 v13 v15 v17 v19 v20 v21
                    (coe v4 v17 v24)
                    (coe
                       v4 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_82 (coe v3))
                       v25)
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0) (coe v9)
                       (coe v13) (coe v17) (coe v4) (coe v26))
                    v27
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v6
        -> case coe v5 of
             C_valid'45'μ'45'wf_892 v12 v14
               -> coe
                    C_valid'45'μ'45'wf_892 v12
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v6) (coe v1))
                       (coe
                          du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v6) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v12) v2)
                       (coe v3) (coe v4) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v6
        -> case coe v5 of
             C_valid'45'ν'45'wf_908 v12 v14
               -> coe
                    C_valid'45'ν'45'wf_908 v12
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3664 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v6) (coe v1))
                       (coe
                          du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v6) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v12) v2)
                       (coe v3) (coe v4) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v5 of
             C_valid'45'int'45'wf_920 v11
               -> coe C_valid'45'int'45'wf_920 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v5 of
             C_valid'45'float'45'wf_932 v11
               -> coe C_valid'45'float'45'wf_932 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v5 of
             C_valid'45'str'45'wf_944 v11
               -> coe C_valid'45'str'45'wf_944 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v5 of
             C_valid'45'buffer'45'wf_956 v11
               -> coe C_valid'45'buffer'45'wf_956 (coe v4 v3 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_3936 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'mem'45'preserved_3936 v0 v1 v2 ~v3 v4 v5 v6 ~v7 v8
                                      v9 ~v10 ~v11 v12
  = du_validityWF'45'mem'45'preserved_3936
      v0 v1 v2 v4 v5 v6 v8 v9 v12
du_validityWF'45'mem'45'preserved_3936 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'mem'45'preserved_3936 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_780))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_806 v20 v21 v23 v24 v25 v28 v29 v30
                           (coe
                              du_fv''_4002 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v11)
                              (coe v6) (coe v7) (coe v20) (coe v23) (coe v28) (coe v31))
                           (coe
                              du_sv''_4004 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                              (coe v12) (coe v6) (coe v7) (coe v21) (coe v24) (coe v29)
                              (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_856 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_4098 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_876 v17 v19 v20 v23 v24
                           (coe
                              du_pv''_4142 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v6)
                              (coe v7) (coe v26) (coe v17) (coe v19) (coe v23) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_836 v12 v15 v16 v18 v20 v22 v23 v24 v27
                    v28
                    (coe
                       du_ev''_4054 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
                       (coe v12) (coe v16) (coe v20) (coe v22) (coe v27) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_892 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_892 v15
                    (coe
                       du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_908 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_908 v15
                    (coe
                       du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                       (coe
                          du_eval_24 v1 v4
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) v5)
                       (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_920 v14 -> coe C_valid'45'int'45'wf_920 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_932 v14
               -> coe C_valid'45'float'45'wf_932 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_944 v14 -> coe C_valid'45'str'45'wf_944 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_956 v14
               -> coe C_valid'45'buffer'45'wf_956 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_3998 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_3998 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_4000 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_4000 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4002 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_fv''_4002 v0 v1 v2 ~v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12 ~v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24 ~v25
  = du_fv''_4002 v0 v1 v2 v4 v5 v7 v10 v11 v14 v16 v21 v24
du_fv''_4002 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_fv''_4002 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4004 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544 -> T_ValidAtWF_544
d_sv''_4004 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 ~v12 ~v13
            ~v14 v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 v25
  = du_sv''_4004 v0 v1 v2 v4 v6 v8 v10 v11 v15 v17 v22 v25
du_sv''_4004 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_sv''_4004 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_4050 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_4050 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_4052 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_4052 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4054 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_BodyCorrect_770 -> T_ValidAtWF_544
d_ev''_4054 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 ~v13
            v14 ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 v24 ~v25
  = du_ev''_4054 v0 v1 v2 v4 v8 v9 v12 v14 v16 v17 v22 v24
du_ev''_4054 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_ev''_4054 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4094 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_4094 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4096 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4096 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4098 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_4098 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_4098 v0 v1 v2 v4 v5 v8 v9 v12 v13 v14 v18 v20
du_pv''_4098 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_4098 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4138 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny
d_tg''_4138 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4140 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4140 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4142 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_pv''_4142 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 ~v10 ~v11 v12 v13 v14
            ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_pv''_4142 v0 v1 v2 v4 v6 v8 v9 v12 v13 v14 v18 v20
du_pv''_4142 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_pv''_4142 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_4280 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'mem'45'preserved'45'excluding_4280 ~v0 ~v1 ~v2 ~v3
                                                   ~v4
  = du_validityWF'45'mem'45'preserved'45'excluding_4280
du_validityWF'45'mem'45'preserved'45'excluding_4280 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'mem'45'preserved'45'excluding_4280
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocInRegions
d_LocInRegions_4288 a0 a1 a2 a3 a4 a5 a6 = ()
data T_LocInRegions_4288
  = C_loc'45'in'45'input_4298 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'fresh_4302 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'anc_4308 AgdaAny | C_loc'45'in'45'heap_4312
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_4330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> Integer -> T_ValidAtWF_544 -> ()
d_LocsInRegions_4330 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_4500 ::
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
  T_LocInRegions_4288 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_4500 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_4572
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\956-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_4594
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\957-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626 v0
                                                                 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18
                                                                 v19 v20
  = du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v19 v20
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626 ::
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
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                  v12 v13 v14 v15
  = case coe v14 of
      C_valid'45'unit'45'wf_780 -> coe C_valid'45'unit'45'wf_780
      C_valid'45'pair'45'wf_806 v23 v24 v26 v27 v28 v31 v32 v33 v34 v35
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
                                                C_valid'45'pair'45'wf_806 v23 v24 v26 v27 v28 v31
                                                v32 v33
                                                (coe
                                                   du_fv''_4712 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v36) (coe v38) (coe v23) (coe v26)
                                                   (coe v31) (coe v34) (coe v44))
                                                (coe
                                                   du_sv''_4714 (coe v0) (coe v1) (coe v2) (coe v5)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v13) (coe v37) (coe v39) (coe v24) (coe v27)
                                                   (coe v32) (coe v35) (coe v45))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_836 v17 v20 v21 v23 v25 v27 v28 v29 v32 v33 v34 v35
        -> case coe v15 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
               -> case coe v37 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                      -> coe
                           C_valid'45'closure'45'wf_836 v17 v20 v21 v23 v25 v27 v28 v29 v32
                           v33
                           (coe
                              du_ev''_4786 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8) (coe v9)
                              (coe v10) (coe v11) (coe v12) (coe v13) (coe v17) (coe v21)
                              (coe v25) (coe v27) (coe v32) (coe v34) (coe v39))
                           v35
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'wf_856 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inl'45'wf_856 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_4846 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v31) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_876 v22 v24 v25 v28 v29 v30
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v31 v32
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v33
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                             -> case coe v35 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                    -> coe
                                         C_valid'45'inr'45'wf_876 v22 v24 v25 v28 v29
                                         (coe
                                            du_pv''_4906 (coe v0) (coe v1) (coe v2) (coe v5)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v13) (coe v32) (coe v33) (coe v22) (coe v24)
                                            (coe v28) (coe v30) (coe v37))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'μ'45'wf_892 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v24
               -> coe
                    C_valid'45'μ'45'wf_892 v21
                    (coe
                       d_μ'45'validity'45'in'45'regions'45'stub_4572 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'ν'45'wf_908 v21 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v24
               -> coe
                    C_valid'45'ν'45'wf_908 v21
                    (coe
                       d_ν'45'validity'45'in'45'regions'45'stub_4594 v0 v1 v2 v3 v5 v24
                       v21 v6 v7 v10 v11 v8 v9 v23)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_920 v21 -> coe C_valid'45'int'45'wf_920 v21
      C_valid'45'float'45'wf_932 v21
        -> coe C_valid'45'float'45'wf_932 v21
      C_valid'45'str'45'wf_944 v21 -> coe C_valid'45'str'45'wf_944 v21
      C_valid'45'buffer'45'wf_956 v21
        -> coe C_valid'45'buffer'45'wf_956 v21
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pl-eq
d_pl'45'eq_4704 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'eq_4704 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.spl-eq
d_spl'45'eq_4706 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_spl'45'eq_4706 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_4708 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_4708 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_4710 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_4710 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4712 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 -> AgdaAny -> AgdaAny -> T_ValidAtWF_544
d_fv''_4712 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 v23 ~v24 ~v25 ~v26 ~v27 v28
            ~v29 ~v30 v31 ~v32 ~v33 ~v34 v35 ~v36
  = du_fv''_4712
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v21 v23 v28 v31 v35
du_fv''_4712 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
du_fv''_4712 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4714 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 -> AgdaAny -> AgdaAny -> T_ValidAtWF_544
d_sv''_4714 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 ~v19 v20 ~v21 v22 ~v23 v24 ~v25 ~v26 ~v27 ~v28
            v29 ~v30 ~v31 v32 ~v33 ~v34 ~v35 v36
  = du_sv''_4714
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v20 v22 v24 v29 v32 v36
du_sv''_4714 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
du_sv''_4714 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cl-eq
d_cl'45'eq_4778 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cl'45'eq_4778 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.scl-eq
d_scl'45'eq_4780 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scl'45'eq_4780 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_4782 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_4782 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_4784 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_4784 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4786 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_BodyCorrect_770 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 -> AgdaAny -> T_ValidAtWF_544
d_ev''_4786 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 ~v19 ~v20 v21 ~v22 v23 v24 ~v25 ~v26 ~v27 ~v28
            v29 ~v30 v31 ~v32 ~v33 ~v34 v35
  = du_ev''_4786
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v21 v23 v24 v29 v31 v35
du_ev''_4786 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
du_ev''_4786 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4840 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 -> T_LocInRegions_4288 -> AgdaAny -> AgdaAny
d_tg''_4840 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_4842 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_4842 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4844 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4844 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4846 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 -> AgdaAny -> T_ValidAtWF_544
d_pv''_4846 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_4846
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v17 v19 v20 v21 v25 v27 v30
du_pv''_4846 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
du_pv''_4846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4900 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 -> T_LocInRegions_4288 -> AgdaAny -> AgdaAny
d_tg''_4900 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_4902 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_4902 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4904 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4904 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4906 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 ->
  T_LocInRegions_4288 ->
  T_LocInRegions_4288 -> AgdaAny -> T_ValidAtWF_544
d_pv''_4906 v0 v1 v2 ~v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12 ~v13 ~v14
            ~v15 ~v16 ~v17 v18 v19 v20 v21 ~v22 ~v23 ~v24 v25 ~v26 v27 ~v28
            ~v29 v30
  = du_pv''_4906
      v0 v1 v2 v4 v6 v7 v8 v9 v11 v12 v18 v19 v20 v21 v25 v27 v30
du_pv''_4906 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny -> T_ValidAtWF_544
du_pv''_4906 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
             v16
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4626
      (coe v0) (coe v1) (coe v2) (coe v13) (coe v10) (coe v3) (coe v11)
      (coe v12) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
      (coe v15) (coe v16)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_5064 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'mem'45'preserved'45'in'45'regions_5064 ~v0 ~v1 ~v2
                                                       ~v3 ~v4
  = du_validityWF'45'mem'45'preserved'45'in'45'regions_5064
du_validityWF'45'mem'45'preserved'45'in'45'regions_5064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'mem'45'preserved'45'in'45'regions_5064
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_5070 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_reclaim'45'alloc_5070 ~v0 ~v1 ~v2 v3 v4
  = du_reclaim'45'alloc_5070 v3 v4
du_reclaim'45'alloc_5070 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_reclaim'45'alloc_5070 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-preserves-frontier
d_reclaim'45'preserves'45'frontier_5084 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_reclaim'45'preserves'45'frontier_5084 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
                                        v7
  = du_reclaim'45'preserves'45'frontier_5084 v5 v6 v7
du_reclaim'45'preserves'45'frontier_5084 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_reclaim'45'preserves'45'frontier_5084 v0 v1 v2
  = coe
      du_stack'45'alloc'45'advances''_5108 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.stack-alloc-advances'
d_stack'45'alloc'45'advances''_5108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_stack'45'alloc'45'advances''_5108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10 v11 v12
  = du_stack'45'alloc'45'advances''_5108 v10 v11 v12
du_stack'45'alloc'45'advances''_5108 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_stack'45'alloc'45'advances''_5108 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_660 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_660
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v8) (coe v0))
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_670 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_670 v7
                    v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_674 v5
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_674 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_5168 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
d_validityWF'45'reclaim_5168 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10
                             ~v11 v12
  = du_validityWF'45'reclaim_5168 v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v12
du_validityWF'45'reclaim_5168 ::
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
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'reclaim_5168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'frontier'45'advance_3302 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v3))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v3)))
      (coe du_reclaim'45'alloc_5070 (coe v3) (coe v8)) (coe v4) (coe v5)
      (coe v6) (coe v7) (coe v9)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v3)))
      (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_5202 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_5202 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.k<start
d_k'60'start_5230 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'start_5230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 v13
  = du_k'60'start_5230 v12 v13
du_k'60'start_5230 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'start_5230 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_5274 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_5274 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_5308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  T_ValidAtWF_544 -> AgdaAny -> AgdaAny -> T_ValidAtWF_544
d_validityWF'45'trace'45'preserves_5308 v0 v1 v2 ~v3 v4 v5 v6 v7
                                        ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_validityWF'45'trace'45'preserves_5308
      v0 v1 v2 v4 v5 v6 v7 v9 v11
du_validityWF'45'trace'45'preserves_5308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_ValidAtWF_544 -> T_ValidAtWF_544
du_validityWF'45'trace'45'preserves_5308 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_validityWF'45'mem'45'preserved_3936 (coe v0) (coe v1) (coe v2)
      (coe v4) (coe v3) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2808 (coe v1)
            (coe v5) (coe v7) (coe v4)))
      (coe v8)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_5346 ::
  T_IRResultAWF_700 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_5346 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_5358 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_5358 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_5390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
d_before'45'frontier'45'monotone_5390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      v7 v8 v9
  = du_before'45'frontier'45'monotone_5390 v7 v8 v9
du_before'45'frontier'45'monotone_5390 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652
du_before'45'frontier'45'monotone_5390 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_660 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_660
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v6) (coe v0))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_670 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_670 v5
             v6 v7 v8
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_674 v4
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_674
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_5472 ::
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
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'compose_5472 = erased
