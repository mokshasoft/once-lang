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
import qualified MAlonzo.Code.Once.CCC.Eval
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump
d_AllocBump_20 a0 a1 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.BeforeFrontier
d_BeforeFrontier_24 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.apply-bump
d_apply'45'bump_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_apply'45'bump_28 ~v0 ~v1 = du_apply'45'bump_28
du_apply'45'bump_28 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_apply'45'bump_28
  = coe MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_912
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_70 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 -> Integer
d_next'45'heap'45'ref'45'delta_70 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'heap'45'ref'45'delta_908
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_72 ::
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 -> Integer
d_next'45'slot'45'delta_72 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_906
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.readLoc
d_readLoc_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_92 ~v0 ~v1 = du_readLoc_92
du_readLoc_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_92
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.write-loc
d_write'45'loc_130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_write'45'loc_130 v0 ~v1 = du_write'45'loc_130 v0
du_write'45'loc_130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_write'45'loc_130 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_write'45'loc_318
      (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.exec-trace
d_exec'45'trace_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_190 v0 ~v1 = du_exec'45'trace_190 v0
du_exec'45'trace_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace_190 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2768 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.TraceWF
d_TraceWF_248 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._._≺_
d__'8826'__432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> AgdaAny -> AgdaAny -> ()
d__'8826'__432 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.Frame
d_Frame_434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> ()
d_Frame_434 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.SumTag
d_SumTag_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_486 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.transport-SumTag
d_transport'45'SumTag_510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_transport'45'SumTag_510 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.prim-sv
d_prim'45'sv_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_prim'45'sv_522 ~v0 ~v1 ~v2 v3 v4 = du_prim'45'sv_522 v3 v4
du_prim'45'sv_522 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_prim'45'sv_522 v0 v1
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
d_ValidAtWF_530 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_ValidAtWF_530
  = C_valid'45'unit'45'wf_766 |
    C_valid'45'pair'45'wf_792 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                              MAlonzo.Code.Once.IR.T_AllocMode_4
                              MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                              T_ValidAtWF_530 T_ValidAtWF_530 |
    C_valid'45'closure'45'wf_822 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                 MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                                 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                                 MAlonzo.Code.Once.IR.T_AllocMode_4 Integer AgdaAny
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                                 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                                 T_ValidAtWF_530 T_BodyCorrect_756 |
    C_valid'45'inl'45'wf_842 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                             T_ValidAtWF_530 |
    C_valid'45'inr'45'wf_862 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                             MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                             T_ValidAtWF_530 |
    C_valid'45'μ'45'wf_878 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                           T_ValidAtWF_530 |
    C_valid'45'ν'45'wf_894 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                           T_ValidAtWF_530 |
    C_valid'45'int'45'wf_906 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_valid'45'float'45'wf_918 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_valid'45'str'45'wf_930 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_valid'45'buffer'45'wf_942 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-primitive-wf
d_valid'45'primitive'45'wf_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ValidAtWF_530
d_valid'45'primitive'45'wf_546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                               v9 ~v10
  = du_valid'45'primitive'45'wf_546 v8 v9
du_valid'45'primitive'45'wf_546 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_510 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530
du_valid'45'primitive'45'wf_546 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_512
        -> coe C_valid'45'int'45'wf_906 v1
      MAlonzo.Code.Once.IRTy.C_fits'45'float_514
        -> coe C_valid'45'float'45'wf_918 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ResultPlace
d_ResultPlace_560 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_ResultPlace_560
  = C_unit'45'result_960 |
    C_at'45'loc_976 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                    T_ValidAtWF_530
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                    T_ValidAtWF_530
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_at'45'reg_994 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                    MAlonzo.Code.Once.IRTy.T_FitsInRegI_510
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                    MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-loc
d_place'45'loc_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_place'45'loc_574 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_place'45'loc_574 v0 v1 v2 v3 v4 v5 v7 v8
du_place'45'loc_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_place'45'loc_574 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_unit'45'result_960
        -> coe
             seq (coe v2)
             (coe d_unit'45'result'45'loc'45'stub_1004 v0 v1 v3 v4 v5 v6)
      C_at'45'loc_976 v14 v15 v16 v18 v19 -> coe v14
      C_at'45'reg_994 v14 v15 v16 v18 -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-before
d_place'45'before_590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_place'45'before_590 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_place'45'before_590 v0 v1 v2 v3 v4 v5 v7 v8
du_place'45'before_590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_place'45'before_590 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_unit'45'result_960
        -> coe seq (coe v2) (coe d_before'45'stub_1016 v0 v1 v3 v4 v5 v6)
      C_at'45'loc_976 v14 v15 v16 v18 v19 -> coe v16
      C_at'45'reg_994 v14 v15 v16 v18 -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-sv
d_place'45'sv_604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_place'45'sv_604 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_unit'45'result_960
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72
                (coe d_unit'45'result'45'sv'45'loc_1028 v0 v1 v3 v4 v5 v7))
      C_at'45'loc_976 v15 v16 v17 v19 v20
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 (coe v15)
      C_at'45'reg_994 v15 v16 v17 v19
        -> coe du_prim'45'sv_522 (coe v16) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-rax
d_place'45'rax_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_place'45'rax_620 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.place-cont-before
d_place'45'cont'45'before_636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_place'45'cont'45'before_636 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_place'45'cont'45'before_636 v0 v1 v2 v3 v4 v5 v7 v8
du_place'45'cont'45'before_636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_place'45'cont'45'before_636 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_unit'45'result_960
        -> coe seq (coe v2) (coe d_before'45'cs_1052 v0 v1 v3 v4 v5 v6)
      C_at'45'loc_976 v14 v15 v16 v18 v19 -> coe v19
      C_at'45'reg_994 v14 v15 v16 v18 -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase
d_IRResultBase_652 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IRResultBase_652
  = C_constructor_1132 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
                       [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900
                       T_ResultPlace_560
                       MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394 AgdaAny
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget
d_IRStackBudget_662 a0 a1 a2 a3 a4 a5 = ()
data T_IRStackBudget_662
  = C_constructor_1204 Integer Integer
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
d_IRHeapBudget_670 a0 a1 a2 a3 a4 = ()
data T_IRHeapBudget_670
  = C_constructor_1234 Integer Integer
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF
d_IRResultAWF_686 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IRResultAWF_686
  = C_constructor_1336 T_IRResultBase_652 T_IRStackBudget_662
                       T_IRHeapBudget_670
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mk-IRResultAWF-via-bump
d_mk'45'IRResultAWF'45'via'45'bump_740 ::
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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  T_IRStackBudget_662 -> T_IRHeapBudget_670 -> T_IRResultAWF_686
d_mk'45'IRResultAWF'45'via'45'bump_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 v9 ~v10 v11 v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 v20
                                       ~v21 v22 v23 v24
  = du_mk'45'IRResultAWF'45'via'45'bump_740
      v9 v11 v12 v17 v20 v22 v23 v24
du_mk'45'IRResultAWF'45'via'45'bump_740 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  T_ResultPlace_560 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394 ->
  AgdaAny ->
  T_IRStackBudget_662 -> T_IRHeapBudget_670 -> T_IRResultAWF_686
du_mk'45'IRResultAWF'45'via'45'bump_740 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1336 (coe C_constructor_1132 v0 v1 v2 v3 v4 v5)
      (coe v6) (coe v7)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect
d_BodyCorrect_756 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_BodyCorrect_756
  = C_constructor_1436 Integer
                       (AgdaAny ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
                        MAlonzo.Code.Once.IR.T_AllocMode_4 ->
                        T_ValidAtWF_530 ->
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-loc-stub
d_unit'45'result'45'loc'45'stub_1004
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-loc-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-stub
d_before'45'stub_1016
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc
d_unit'45'result'45'sv'45'loc_1028
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.unit-result-sv-loc"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub
d_rax'45'stub_1040
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.rax-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-cs
d_before'45'cs_1052
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.before-cs"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-state
d_final'45'state_1098 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_final'45'state_1098 v0
  = case coe v0 of
      C_constructor_1132 v1 v2 v3 v7 v10 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace
d_trace_1100 ::
  T_IRResultBase_652 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_trace_1100 v0
  = case coe v0 of
      C_constructor_1132 v1 v2 v3 v7 v10 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.bump
d_bump_1102 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900
d_bump_1102 v0
  = case coe v0 of
      C_constructor_1132 v1 v2 v3 v7 v10 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1104 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1104 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-correct
d_trace'45'correct_1106 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1106 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.alloc-correct
d_alloc'45'correct_1108 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1108 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.result-place
d_result'45'place_1110 :: T_IRResultBase_652 -> T_ResultPlace_560
d_result'45'place_1110 v0
  = case coe v0 of
      C_constructor_1132 v1 v2 v3 v7 v10 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.not-halted
d_not'45'halted_1112 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1112 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.mem-preserved-before
d_mem'45'preserved'45'before_1116 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1116 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-twf
d_trace'45'twf_1118 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394
d_trace'45'twf_1118 v0
  = case coe v0 of
      C_constructor_1132 v1 v2 v3 v7 v10 v12 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-preserves-halted
d_trace'45'preserves'45'halted_1124 ::
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1124 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1126 :: T_IRResultBase_652 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1126 v0
  = case coe v0 of
      C_constructor_1132 v1 v2 v3 v7 v10 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.final-alloc
d_final'45'alloc_1128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_final'45'alloc_1128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_final'45'alloc_1128 v8 v9
du_final'45'alloc_1128 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultBase_652 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_final'45'alloc_1128 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_apply'45'bump_912
      (coe d_bump_1102 (coe v1)) (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultBase.frame-preserved
d_frame'45'preserved_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultBase_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1130 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-written
d_max'45'slot'45'written_1170 :: T_IRStackBudget_662 -> Integer
d_max'45'slot'45'written_1170 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.stack-budget
d_stack'45'budget_1172 :: T_IRStackBudget_662 -> Integer
d_stack'45'budget_1172 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1174 ::
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1174 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1176 ::
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1176 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1178 ::
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1178 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.frontier-slot-stable
d_frontier'45'slot'45'stable_1184 ::
  T_IRStackBudget_662 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1184 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-above
d_trace'45'writes'45'above_1186 :: T_IRStackBudget_662 -> AgdaAny
d_trace'45'writes'45'above_1186 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1188 ::
  T_IRStackBudget_662 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1188 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-writes-below
d_trace'45'writes'45'below_1190 :: T_IRStackBudget_662 -> AgdaAny
d_trace'45'writes'45'below_1190 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1192 ::
  T_IRStackBudget_662 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1192 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-budget
d_scratch'45'budget_1194 :: T_IRStackBudget_662 -> Integer
d_scratch'45'budget_1194 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.scratch-bounded
d_scratch'45'bounded_1196 ::
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1196 v0
  = case coe v0 of
      C_constructor_1204 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-monotone
d_slot'45'monotone_1198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1198 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_slot'45'monotone_1198 v2
du_slot'45'monotone_1198 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1198 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRStackBudget.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1200 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_slot'45'stays'45'in'45'budget_1200 v2 v3 v6
du_slot'45'stays'45'in'45'budget_1200 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  T_IRStackBudget_662 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1200 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.Allocation.d_next'45'slot'45'delta_906
         (coe v1))
      (d_stack'45'budget_1172 (coe v2))
      (d_bump'45'fits'45'stack'45'budget_1174 (coe v2))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-budget
d_heap'45'budget_1222 :: T_IRHeapBudget_670 -> Integer
d_heap'45'budget_1222 v0
  = case coe v0 of
      C_constructor_1234 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1224 ::
  T_IRHeapBudget_670 -> Integer
d_max'45'heap'45'ref'45'written_1224 v0
  = case coe v0 of
      C_constructor_1234 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1226 ::
  T_IRHeapBudget_670 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1226 v0
  = case coe v0 of
      C_constructor_1234 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1228 ::
  T_IRHeapBudget_670 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1228 v0
  = case coe v0 of
      C_constructor_1234 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1230 ::
  T_IRHeapBudget_670 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1230 v0
  = case coe v0 of
      C_constructor_1234 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRHeapBudget.heap-monotone
d_heap'45'monotone_1232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_IRHeapBudget_670 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1232 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_heap'45'monotone_1232 v2
du_heap'45'monotone_1232 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1232 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.base
d_base_1256 :: T_IRResultAWF_686 -> T_IRResultBase_652
d_base_1256 v0
  = case coe v0 of
      C_constructor_1336 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.stack-inv
d_stack'45'inv_1258 :: T_IRResultAWF_686 -> T_IRStackBudget_662
d_stack'45'inv_1258 v0
  = case coe v0 of
      C_constructor_1336 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF.heap-inv
d_heap'45'inv_1260 :: T_IRResultAWF_686 -> T_IRHeapBudget_670
d_heap'45'inv_1260 v0
  = case coe v0 of
      C_constructor_1336 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.alloc-correct
d_alloc'45'correct_1264 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alloc'45'correct_1264 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump
d_bump_1266 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_AllocBump_900
d_bump_1266 v0 = coe d_bump_1102 (coe d_base_1256 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-alloc
d_final'45'alloc_1268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_final'45'alloc_1268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_final'45'alloc_1268 v8 v9
du_final'45'alloc_1268 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_final'45'alloc_1268 v0 v1
  = coe du_final'45'alloc_1128 (coe v0) (coe d_base_1256 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.final-state
d_final'45'state_1270 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_final'45'state_1270 v0
  = coe d_final'45'state_1098 (coe d_base_1256 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frame-preserved
d_frame'45'preserved_1272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'preserved_1272 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.mem-preserved-before
d_mem'45'preserved'45'before_1274 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'before_1274 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.not-halted
d_not'45'halted_1276 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'halted_1276 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.result-place
d_result'45'place_1278 :: T_IRResultAWF_686 -> T_ResultPlace_560
d_result'45'place_1278 v0
  = coe d_result'45'place_1110 (coe d_base_1256 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace
d_trace_1280 ::
  T_IRResultAWF_686 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188]
d_trace_1280 v0 = coe d_trace_1100 (coe d_base_1256 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-correct
d_trace'45'correct_1282 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'correct_1282 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-is-ir-to-trace
d_trace'45'is'45'ir'45'to'45'trace_1284 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'is'45'ir'45'to'45'trace_1284 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-no-frame-ops
d_trace'45'no'45'frame'45'ops_1286 :: T_IRResultAWF_686 -> AgdaAny
d_trace'45'no'45'frame'45'ops_1286 v0
  = coe d_trace'45'no'45'frame'45'ops_1126 (coe d_base_1256 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-preserves-halted
d_trace'45'preserves'45'halted_1288 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'45'preserves'45'halted_1288 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-twf
d_trace'45'twf_1290 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.SMPrimitives.T_TraceWF_8394
d_trace'45'twf_1290 v0
  = coe d_trace'45'twf_1118 (coe d_base_1256 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-stack-budget
d_bump'45'fits'45'stack'45'budget_1294 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'stack'45'budget_1294 v0
  = coe
      d_bump'45'fits'45'stack'45'budget_1174
      (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.frontier-slot-stable
d_frontier'45'slot'45'stable_1296 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_frontier'45'slot'45'stable_1296 v0
  = coe
      d_frontier'45'slot'45'stable_1184
      (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-geq-final
d_max'45'slot'45'geq'45'final_1298 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'geq'45'final_1298 v0
  = coe
      d_max'45'slot'45'geq'45'final_1176
      (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-usage-bound
d_max'45'slot'45'usage'45'bound_1300 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'slot'45'usage'45'bound_1300 v0
  = coe
      d_max'45'slot'45'usage'45'bound_1178
      (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-slot-written
d_max'45'slot'45'written_1302 :: T_IRResultAWF_686 -> Integer
d_max'45'slot'45'written_1302 v0
  = coe
      d_max'45'slot'45'written_1170 (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-bounded
d_scratch'45'bounded_1304 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'bounded_1304 v0
  = coe d_scratch'45'bounded_1196 (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.scratch-budget
d_scratch'45'budget_1306 :: T_IRResultAWF_686 -> Integer
d_scratch'45'budget_1306 v0
  = coe d_scratch'45'budget_1194 (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-monotone
d_slot'45'monotone_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'monotone_1308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_slot'45'monotone_1308 v8
du_slot'45'monotone_1308 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'monotone_1308 v0 = coe du_slot'45'monotone_1198 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.slot-stays-in-budget
d_slot'45'stays'45'in'45'budget_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'stays'45'in'45'budget_1310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 v8 v9
  = du_slot'45'stays'45'in'45'budget_1310 v8 v9
du_slot'45'stays'45'in'45'budget_1310 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'stays'45'in'45'budget_1310 v0 v1
  = coe
      du_slot'45'stays'45'in'45'budget_1200 (coe v0)
      (coe d_bump_1102 (coe d_base_1256 (coe v1)))
      (coe d_stack'45'inv_1258 (coe v1))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.stack-budget
d_stack'45'budget_1312 :: T_IRResultAWF_686 -> Integer
d_stack'45'budget_1312 v0
  = coe d_stack'45'budget_1172 (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-above
d_trace'45'slot'45'reads'45'above_1314 ::
  T_IRResultAWF_686 -> AgdaAny
d_trace'45'slot'45'reads'45'above_1314 v0
  = coe
      d_trace'45'slot'45'reads'45'above_1188
      (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-slot-reads-below
d_trace'45'slot'45'reads'45'below_1316 ::
  T_IRResultAWF_686 -> AgdaAny
d_trace'45'slot'45'reads'45'below_1316 v0
  = coe
      d_trace'45'slot'45'reads'45'below_1192
      (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-above
d_trace'45'writes'45'above_1318 :: T_IRResultAWF_686 -> AgdaAny
d_trace'45'writes'45'above_1318 v0
  = coe
      d_trace'45'writes'45'above_1186 (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.trace-writes-below
d_trace'45'writes'45'below_1320 :: T_IRResultAWF_686 -> AgdaAny
d_trace'45'writes'45'below_1320 v0
  = coe
      d_trace'45'writes'45'below_1190 (coe d_stack'45'inv_1258 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.bump-fits-heap-budget
d_bump'45'fits'45'heap'45'budget_1324 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bump'45'fits'45'heap'45'budget_1324 v0
  = coe
      d_bump'45'fits'45'heap'45'budget_1226
      (coe d_heap'45'inv_1260 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-budget
d_heap'45'budget_1326 :: T_IRResultAWF_686 -> Integer
d_heap'45'budget_1326 v0
  = coe d_heap'45'budget_1222 (coe d_heap'45'inv_1260 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.heap-monotone
d_heap'45'monotone_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_heap'45'monotone_1328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_heap'45'monotone_1328 v8
du_heap'45'monotone_1328 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_heap'45'monotone_1328 v0 = coe du_heap'45'monotone_1232 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-geq-final
d_max'45'heap'45'ref'45'geq'45'final_1330 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'ref'45'geq'45'final_1330 v0
  = coe
      d_max'45'heap'45'ref'45'geq'45'final_1228
      (coe d_heap'45'inv_1260 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-ref-written
d_max'45'heap'45'ref'45'written_1332 ::
  T_IRResultAWF_686 -> Integer
d_max'45'heap'45'ref'45'written_1332 v0
  = coe
      d_max'45'heap'45'ref'45'written_1224
      (coe d_heap'45'inv_1260 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.IRResultAWF._.max-heap-usage-bound
d_max'45'heap'45'usage'45'bound_1334 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_max'45'heap'45'usage'45'bound_1334 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1230
      (coe d_heap'45'inv_1260 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-capacity
d_body'45'capacity_1416 :: T_BodyCorrect_756 -> Integer
d_body'45'capacity_1416 v0
  = case coe v0 of
      C_constructor_1436 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.body-cap-eq
d_body'45'cap'45'eq_1418 ::
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'cap'45'eq_1418 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.BodyCorrect.execute
d_execute_1434 ::
  T_BodyCorrect_756 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_execute_1434 v0
  = case coe v0 of
      C_constructor_1436 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.heap-preserved-of
d_heap'45'preserved'45'of_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'preserved'45'of_1454 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-via-budget
d_bound'45'via'45'budget_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'via'45'budget_1466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9 ~v10
  = du_bound'45'via'45'budget_1466 v9
du_bound'45'via'45'budget_1466 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'via'45'budget_1466 v0
  = coe
      d_max'45'heap'45'usage'45'bound_1230
      (coe d_heap'45'inv_1260 (coe v0))
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.bound-alloc
d_bound'45'alloc_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_IRResultAWF_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bound'45'alloc_1470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10
  = du_bound'45'alloc_1470 v9
du_bound'45'alloc_1470 ::
  T_IRResultAWF_686 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_bound'45'alloc_1470 v0
  = coe du_bound'45'via'45'budget_1466 (coe v0)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed
d_ClosureWellFormed_1496 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_ClosureWellFormed_1496
  = C_constructor_1552 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.IR.T_AllocMode_4 T_ValidAtWF_530
                       T_BodyCorrect_756
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-ptr
d_env'45'ptr_1536 ::
  T_ClosureWellFormed_1496 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1536 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-ptr
d_code'45'ptr_1538 ::
  T_ClosureWellFormed_1496 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1538 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-before
d_env'45'before_1540 ::
  T_ClosureWellFormed_1496 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_env'45'before_1540 v0
  = case coe v0 of
      C_constructor_1552 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.code-before
d_code'45'before_1542 ::
  T_ClosureWellFormed_1496 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_code'45'before_1542 v0
  = case coe v0 of
      C_constructor_1552 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.sucLoc-before
d_sucLoc'45'before_1544 ::
  T_ClosureWellFormed_1496 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_1544 v0
  = case coe v0 of
      C_constructor_1552 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.mEnv
d_mEnv_1546 ::
  T_ClosureWellFormed_1496 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1546 v0
  = case coe v0 of
      C_constructor_1552 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.env-valid
d_env'45'valid_1548 :: T_ClosureWellFormed_1496 -> T_ValidAtWF_530
d_env'45'valid_1548 v0
  = case coe v0 of
      C_constructor_1552 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureWellFormed.body-correct
d_body'45'correct_1550 ::
  T_ClosureWellFormed_1496 -> T_BodyCorrect_756
d_body'45'correct_1550 v0
  = case coe v0 of
      C_constructor_1552 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF
d_ClosureValidWF_1566 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_ClosureValidWF_1566
  = C_constructor_1640 MAlonzo.Code.Once.IRTy.T_IRTy_6
                       MAlonzo.Code.Once.IR.T_IR_16 AgdaAny
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 Integer
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ValidAtWF_530 T_BodyCorrect_756
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.EnvType
d_EnvType_1610 ::
  T_ClosureValidWF_1566 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_EnvType_1610 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body
d_body_1612 ::
  T_ClosureValidWF_1566 -> MAlonzo.Code.Once.IR.T_IR_16
d_body_1612 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env
d_env_1614 :: T_ClosureValidWF_1566 -> AgdaAny
d_env_1614 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body<bound
d_body'60'bound_1616 ::
  T_ClosureValidWF_1566 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_body'60'bound_1616 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-loc
d_env'45'loc_1618 ::
  T_ClosureValidWF_1566 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_env'45'loc_1618 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-label
d_body'45'label_1620 :: T_ClosureValidWF_1566 -> Integer
d_body'45'label_1620 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.mEnv
d_mEnv_1622 ::
  T_ClosureValidWF_1566 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mEnv_1622 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-ptr
d_env'45'ptr_1624 ::
  T_ClosureValidWF_1566 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'ptr_1624 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.code-ptr
d_code'45'ptr_1626 ::
  T_ClosureValidWF_1566 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'45'ptr_1626 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-before
d_env'45'before_1628 ::
  T_ClosureValidWF_1566 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_env'45'before_1628 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.sucLoc-before
d_sucLoc'45'before_1630 ::
  T_ClosureValidWF_1566 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_1630 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.env-valid
d_env'45'valid_1632 :: T_ClosureValidWF_1566 -> T_ValidAtWF_530
d_env'45'valid_1632 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.body-correct
d_body'45'correct_1634 ::
  T_ClosureValidWF_1566 -> T_BodyCorrect_756
d_body'45'correct_1634 v0
  = case coe v0 of
      C_constructor_1640 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ClosureValidWF.f-is-closure
d_f'45'is'45'closure_1638 ::
  T_ClosureValidWF_1566 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'45'is'45'closure_1638 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeClosureWF
d_decomposeClosureWF_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_ClosureValidWF_1566
d_decomposeClosureWF_1656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_decomposeClosureWF_1656 v9
du_decomposeClosureWF_1656 ::
  T_ValidAtWF_530 -> T_ClosureValidWF_1566
du_decomposeClosureWF_1656 v0
  = case coe v0 of
      C_valid'45'closure'45'wf_822 v2 v5 v6 v8 v10 v12 v13 v14 v17 v18 v19 v20
        -> coe C_constructor_1640 v2 v5 v6 v8 v10 v13 v12 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.RecDispatcherWF
d_RecDispatcherWF_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> Integer -> ()
d_RecDispatcherWF_1686 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF
d_PairValidWF_1720 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_PairValidWF_1720
  = C_constructor_1778 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ValidAtWF_530 T_ValidAtWF_530
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-loc
d_fst'45'loc_1756 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_fst'45'loc_1756 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-loc
d_snd'45'loc_1758 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_snd'45'loc_1758 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mA
d_mA_1760 ::
  T_PairValidWF_1720 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1760 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.mB
d_mB_1762 ::
  T_PairValidWF_1720 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1762 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-ptr
d_fst'45'ptr_1764 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fst'45'ptr_1764 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-ptr
d_snd'45'ptr_1766 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_snd'45'ptr_1766 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-before
d_fst'45'before_1768 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_fst'45'before_1768 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-before
d_snd'45'before_1770 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_snd'45'before_1770 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.sucLoc-before
d_sucLoc'45'before_1772 ::
  T_PairValidWF_1720 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_1772 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.fst-valid
d_fst'45'valid_1774 :: T_PairValidWF_1720 -> T_ValidAtWF_530
d_fst'45'valid_1774 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.PairValidWF.snd-valid
d_snd'45'valid_1776 :: T_PairValidWF_1720 -> T_ValidAtWF_530
d_snd'45'valid_1776 v0
  = case coe v0 of
      C_constructor_1778 v1 v2 v3 v4 v7 v8 v9 v10 v11 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposePairWF
d_decomposePairWF_1794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_PairValidWF_1720
d_decomposePairWF_1794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_decomposePairWF_1794 v9
du_decomposePairWF_1794 :: T_ValidAtWF_530 -> T_PairValidWF_1720
du_decomposePairWF_1794 v0
  = case coe v0 of
      C_valid'45'pair'45'wf_792 v8 v9 v11 v12 v13 v16 v17 v18 v19 v20
        -> coe C_constructor_1778 v8 v9 v11 v12 v16 v17 v18 v19 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF
d_InlValidWF_1832 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InlValidWF_1832
  = C_constructor_1878 AgdaAny MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ValidAtWF_530
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.a
d_a_1862 :: T_InlValidWF_1832 -> AgdaAny
d_a_1862 v0
  = case coe v0 of
      C_constructor_1878 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.mA
d_mA_1864 ::
  T_InlValidWF_1832 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mA_1864 v0
  = case coe v0 of
      C_constructor_1878 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-loc
d_payload'45'loc_1866 ::
  T_InlValidWF_1832 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_1866 v0
  = case coe v0 of
      C_constructor_1878 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-ptr
d_payload'45'ptr_1868 ::
  T_InlValidWF_1832 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_1868 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-before
d_payload'45'before_1870 ::
  T_InlValidWF_1832 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_payload'45'before_1870 v0
  = case coe v0 of
      C_constructor_1878 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.sucLoc-before
d_sucLoc'45'before_1872 ::
  T_InlValidWF_1832 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_1872 v0
  = case coe v0 of
      C_constructor_1878 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.payload-valid
d_payload'45'valid_1874 :: T_InlValidWF_1832 -> T_ValidAtWF_530
d_payload'45'valid_1874 v0
  = case coe v0 of
      C_constructor_1878 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InlValidWF.v-is-inl
d_v'45'is'45'inl_1876 ::
  T_InlValidWF_1832 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inl_1876 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF
d_InrValidWF_1892 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_InrValidWF_1892
  = C_constructor_1938 AgdaAny MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ValidAtWF_530
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.b
d_b_1922 :: T_InrValidWF_1892 -> AgdaAny
d_b_1922 v0
  = case coe v0 of
      C_constructor_1938 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.mB
d_mB_1924 ::
  T_InrValidWF_1892 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_mB_1924 v0
  = case coe v0 of
      C_constructor_1938 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-loc
d_payload'45'loc_1926 ::
  T_InrValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_payload'45'loc_1926 v0
  = case coe v0 of
      C_constructor_1938 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-ptr
d_payload'45'ptr_1928 ::
  T_InrValidWF_1892 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_payload'45'ptr_1928 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-before
d_payload'45'before_1930 ::
  T_InrValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_payload'45'before_1930 v0
  = case coe v0 of
      C_constructor_1938 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.sucLoc-before
d_sucLoc'45'before_1932 ::
  T_InrValidWF_1892 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sucLoc'45'before_1932 v0
  = case coe v0 of
      C_constructor_1938 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.payload-valid
d_payload'45'valid_1934 :: T_InrValidWF_1892 -> T_ValidAtWF_530
d_payload'45'valid_1934 v0
  = case coe v0 of
      C_constructor_1938 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.InrValidWF.v-is-inr
d_v'45'is'45'inr_1936 ::
  T_InrValidWF_1892 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_v'45'is'45'inr_1936 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInlWF
d_decomposeInlWF_1954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_InlValidWF_1832
d_decomposeInlWF_1954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_decomposeInlWF_1954 v6 v9
du_decomposeInlWF_1954 ::
  AgdaAny -> T_ValidAtWF_530 -> T_InlValidWF_1832
du_decomposeInlWF_1954 v0 v1
  = case coe v1 of
      C_valid'45'inl'45'wf_842 v8 v10 v11 v14 v15 v16
        -> coe C_constructor_1878 v0 v10 v8 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.decomposeInrWF
d_decomposeInrWF_1990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_InrValidWF_1892
d_decomposeInrWF_1990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_decomposeInrWF_1990 v6 v9
du_decomposeInrWF_1990 ::
  AgdaAny -> T_ValidAtWF_530 -> T_InrValidWF_1892
du_decomposeInrWF_1990 v0 v1
  = case coe v1 of
      C_valid'45'inr'45'wf_862 v8 v10 v11 v14 v15 v16
        -> coe C_constructor_1938 v0 v10 v8 v14 v15 v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.valid-to-validWF-unit
d_valid'45'to'45'validWF'45'unit_2020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530
d_valid'45'to'45'validWF'45'unit_2020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_valid'45'to'45'validWF'45'unit_2020
du_valid'45'to'45'validWF'45'unit_2020 :: T_ValidAtWF_530
du_valid'45'to'45'validWF'45'unit_2020
  = coe C_valid'45'unit'45'wf_766
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-only
d_validityWF'45'mem'45'only_2036 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'mem'45'only_2036 v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 ~v9
                                 ~v10 v11
  = du_validityWF'45'mem'45'only_2036 v0 v1 v3 v4 v5 v7 v8 v11
du_validityWF'45'mem'45'only_2036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'mem'45'only_2036 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v4) (coe seq (coe v7) (coe C_valid'45'unit'45'wf_766))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29 v30 v31
                      -> coe
                           C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29
                           (coe
                              du_fv''_2102 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v19) (coe v22) (coe v30))
                           (coe
                              du_sv''_2104 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v20) (coe v23) (coe v31))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25
                      -> coe
                           C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_2198 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25
                      -> coe
                           C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_2242 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26 v27 v28 v29
               -> coe
                    C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26
                    v27
                    (coe
                       du_ev''_2154 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v11)
                       (coe v15) (coe v19) (coe v21) (coe v28))
                    v29
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
        -> case coe v7 of
             C_valid'45'μ'45'wf_878 v14 v16
               -> coe
                    C_valid'45'μ'45'wf_878 v14
                    (coe
                       du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
        -> case coe v7 of
             C_valid'45'ν'45'wf_894 v14 v16
               -> coe
                    C_valid'45'ν'45'wf_894 v14
                    (coe
                       du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v7 of
             C_valid'45'int'45'wf_906 v13 -> coe C_valid'45'int'45'wf_906 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v7 of
             C_valid'45'float'45'wf_918 v13
               -> coe C_valid'45'float'45'wf_918 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v7 of
             C_valid'45'str'45'wf_930 v13 -> coe C_valid'45'str'45'wf_930 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v7 of
             C_valid'45'buffer'45'wf_942 v13
               -> coe C_valid'45'buffer'45'wf_942 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2098 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2098 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2100 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2100 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2102 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_fv''_2102 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 v13
            ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24
  = du_fv''_2102 v0 v1 v3 v4 v6 v9 v10 v13 v15 v23
du_fv''_2102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_fv''_2102 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2104 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_sv''_2104 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 ~v12 ~v13
            v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_sv''_2104 v0 v1 v3 v5 v7 v9 v10 v14 v16 v24
du_sv''_2104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_sv''_2104 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2150 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2150 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2152 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2152 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2154 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_BodyCorrect_756 -> T_ValidAtWF_530
d_ev''_2154 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24
  = du_ev''_2154 v0 v1 v3 v7 v8 v11 v13 v15 v16 v23
du_ev''_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_ev''_2154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
      (coe v5) (coe v6) (coe v3) (coe v4) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2194 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_2194 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2196 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2196 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2198 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_2198 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 ~v17 ~v18 v19
  = du_pv''_2198 v0 v1 v3 v4 v7 v8 v11 v12 v13 v19
du_pv''_2198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_2198 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v4) (coe v5) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2238 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_2238 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2240 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2240 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2242 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_2242 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 ~v17 ~v18 v19
  = du_pv''_2242 v0 v1 v3 v5 v7 v8 v11 v12 v13 v19
du_pv''_2242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_2242 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'mem'45'only_2036 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v4) (coe v5) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-frontier
d_validityWF'45'write'45'at'45'frontier_2370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'write'45'at'45'frontier_2370 v0 v1 ~v2 v3 v4 v5 ~v6
                                             v7 v8 ~v9 v10
  = du_validityWF'45'write'45'at'45'frontier_2370
      v0 v1 v3 v4 v5 v7 v8 v10
du_validityWF'45'write'45'at'45'frontier_2370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'write'45'at'45'frontier_2370 v0 v1 v2 v3 v4 v5 v6
                                              v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v7) (coe C_valid'45'unit'45'wf_766)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29 v30 v31
                      -> coe
                           C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29
                           (coe
                              du_fv''_2432 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v19) (coe v22) (coe v27) (coe v30))
                           (coe
                              du_sv''_2434 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v20) (coe v23) (coe v28) (coe v31))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25
                      -> coe
                           C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_2524 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v22) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25
                      -> coe
                           C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_2566 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v22) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26 v27 v28 v29
               -> coe
                    C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26
                    v27
                    (coe
                       du_ev''_2482 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v11)
                       (coe v15) (coe v19) (coe v21) (coe v26) (coe v28))
                    v29
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
        -> case coe v7 of
             C_valid'45'μ'45'wf_878 v14 v16
               -> coe
                    C_valid'45'μ'45'wf_878 v14
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
        -> case coe v7 of
             C_valid'45'ν'45'wf_894 v14 v16
               -> coe
                    C_valid'45'ν'45'wf_894 v14
                    (coe
                       du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v7 of
             C_valid'45'int'45'wf_906 v13 -> coe C_valid'45'int'45'wf_906 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v7 of
             C_valid'45'float'45'wf_918 v13
               -> coe C_valid'45'float'45'wf_918 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v7 of
             C_valid'45'str'45'wf_930 v13 -> coe C_valid'45'str'45'wf_930 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v7 of
             C_valid'45'buffer'45'wf_942 v13
               -> coe C_valid'45'buffer'45'wf_942 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2428 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2428 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2430 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2430 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2432 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_fv''_2432 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9 v10 ~v11 v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 v22 ~v23
  = du_fv''_2432 v0 v1 v3 v4 v6 v9 v10 v12 v14 v19 v22
du_fv''_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_fv''_2432 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2434 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_sv''_2434 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 ~v12 v13
            ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23
  = du_sv''_2434 v0 v1 v3 v5 v7 v9 v10 v13 v15 v20 v23
du_sv''_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_sv''_2434 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2478 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2480 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_BodyCorrect_756 -> T_ValidAtWF_530
d_ev''_2482 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10 ~v11 v12 ~v13
            v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 v22 ~v23
  = du_ev''_2482 v0 v1 v3 v7 v8 v10 v12 v14 v15 v20 v22
du_ev''_2482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_ev''_2482 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
      (coe v2) (coe v5) (coe v6) (coe v3) (coe v4) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_2520 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2522 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_2524 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 ~v9 v10 v11 v12 ~v13 ~v14
            ~v15 v16 ~v17 v18
  = du_pv''_2524 v0 v1 v3 v4 v7 v8 v10 v11 v12 v16 v18
du_pv''_2524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_2524 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_2562 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2564 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_2566 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 v10 v11 v12 ~v13 ~v14
            ~v15 v16 ~v17 v18
  = du_pv''_2566 v0 v1 v3 v5 v7 v8 v10 v11 v12 v16 v18
du_pv''_2566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_2566 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'frontier_2370 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v6) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-write-at-suc-frontier
d_validityWF'45'write'45'at'45'suc'45'frontier_2682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'write'45'at'45'suc'45'frontier_2682 v0 v1 ~v2 v3 v4
                                                    v5 ~v6 v7 v8 ~v9 v10
  = du_validityWF'45'write'45'at'45'suc'45'frontier_2682
      v0 v1 v3 v4 v5 v7 v8 v10
du_validityWF'45'write'45'at'45'suc'45'frontier_2682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'write'45'at'45'suc'45'frontier_2682 v0 v1 v2 v3 v4
                                                     v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe seq (coe v7) (coe C_valid'45'unit'45'wf_766)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29 v30 v31
                      -> coe
                           C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29
                           (coe
                              du_fv''_2744 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v19) (coe v22) (coe v27) (coe v30))
                           (coe
                              du_sv''_2746 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v20) (coe v23) (coe v28) (coe v31))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25
                      -> coe
                           C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_2836 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v22) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25
                      -> coe
                           C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_2878 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v22) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26 v27 v28 v29
               -> coe
                    C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26
                    v27
                    (coe
                       du_ev''_2794 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v11)
                       (coe v15) (coe v19) (coe v21) (coe v26) (coe v28))
                    v29
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
        -> case coe v7 of
             C_valid'45'μ'45'wf_878 v14 v16
               -> coe
                    C_valid'45'μ'45'wf_878 v14
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
                       (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
        -> case coe v7 of
             C_valid'45'ν'45'wf_894 v14 v16
               -> coe
                    C_valid'45'ν'45'wf_894 v14
                    (coe
                       du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
                       (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v7 of
             C_valid'45'int'45'wf_906 v13 -> coe C_valid'45'int'45'wf_906 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v7 of
             C_valid'45'float'45'wf_918 v13
               -> coe C_valid'45'float'45'wf_918 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v7 of
             C_valid'45'str'45'wf_930 v13 -> coe C_valid'45'str'45'wf_930 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v7 of
             C_valid'45'buffer'45'wf_942 v13
               -> coe C_valid'45'buffer'45'wf_942 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_2740 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_2740 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_2742 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_2742 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_2744 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_fv''_2744 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9 v10 ~v11 v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 v22 ~v23
  = du_fv''_2744 v0 v1 v3 v4 v6 v9 v10 v12 v14 v19 v22
du_fv''_2744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_fv''_2744 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_2746 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_sv''_2746 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 ~v12 v13
            ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23
  = du_sv''_2746 v0 v1 v3 v5 v7 v9 v10 v13 v15 v20 v23
du_sv''_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_sv''_2746 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_2790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_2790 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_2792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_2792 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_2794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_BodyCorrect_756 -> T_ValidAtWF_530
d_ev''_2794 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10 ~v11 v12 ~v13
            v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 v22 ~v23
  = du_ev''_2794 v0 v1 v3 v7 v8 v10 v12 v14 v15 v20 v22
du_ev''_2794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_ev''_2794 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
      (coe v1) (coe v2) (coe v5) (coe v6) (coe v3) (coe v4) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_2832 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2834 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_2836 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 ~v9 v10 v11 v12 ~v13 ~v14
            ~v15 v16 ~v17 v18
  = du_pv''_2836 v0 v1 v3 v4 v7 v8 v10 v11 v12 v16 v18
du_pv''_2836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_2836 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_2874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_2874 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_2876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_2876 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_2878 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 v10 v11 v12 ~v13 ~v14
            ~v15 v16 ~v17 v18
  = du_pv''_2878 v0 v1 v3 v5 v7 v8 v10 v11 v12 v16 v18
du_pv''_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_2878 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'write'45'at'45'suc'45'frontier_2682 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v6) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-alloc-advance
d_validityWF'45'alloc'45'advance_2996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'alloc'45'advance_2996 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
                                      v9
  = du_validityWF'45'alloc'45'advance_2996 v0 v1 v3 v4 v5 v6 v7 v8 v9
du_validityWF'45'alloc'45'advance_2996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer -> T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'alloc'45'advance_2996 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v4) (coe seq (coe v8) (coe C_valid'45'unit'45'wf_766))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> case coe v8 of
                    C_valid'45'pair'45'wf_792 v20 v21 v23 v24 v25 v28 v29 v30 v31 v32
                      -> coe
                           C_valid'45'pair'45'wf_792 v20 v21 v23 v24 v25
                           (coe du_fb''_3050 (coe v2) (coe v20) (coe v28))
                           (coe du_sb''_3052 (coe v2) (coe v21) (coe v29))
                           (coe du_slb''_3054 (coe v2) (coe v5) (coe v30))
                           (coe
                              du_fv''_3056 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v6)
                              (coe v7) (coe v20) (coe v23) (coe v31))
                           (coe
                              du_sv''_3058 (coe v0) (coe v1) (coe v2) (coe v10) (coe v12)
                              (coe v6) (coe v7) (coe v21) (coe v24) (coe v32))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
        -> case coe v8 of
             C_valid'45'inl'45'wf_842 v17 v19 v20 v23 v24 v25
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_valid'45'inl'45'wf_842 v17 v19 v20
                           (coe du_pb''_3140 (coe v2) (coe v17) (coe v23))
                           (coe du_slb''_3142 (coe v2) (coe v5) (coe v24))
                           (coe
                              du_pv''_3144 (coe v0) (coe v1) (coe v2) (coe v9) (coe v6) (coe v7)
                              (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v17 v19 v20 v23 v24 v25
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_valid'45'inr'45'wf_862 v17 v19 v20
                           (coe du_pb''_3180 (coe v2) (coe v17) (coe v23))
                           (coe du_slb''_3182 (coe v2) (coe v5) (coe v24))
                           (coe
                              du_pv''_3184 (coe v0) (coe v1) (coe v2) (coe v10) (coe v6) (coe v7)
                              (coe v26) (coe v17) (coe v19) (coe v25))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
        -> case coe v8 of
             C_valid'45'closure'45'wf_822 v12 v15 v16 v18 v20 v22 v23 v24 v27 v28 v29 v30
               -> coe
                    C_valid'45'closure'45'wf_822 v12 v15 v16 v18 v20 v22 v23 v24
                    (coe du_eb''_3100 (coe v2) (coe v20) (coe v27))
                    (coe du_slb''_3102 (coe v2) (coe v5) (coe v28))
                    (coe
                       du_ev''_3104 (coe v0) (coe v1) (coe v2) (coe v6) (coe v7) (coe v12)
                       (coe v16) (coe v20) (coe v22) (coe v29))
                    v30
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
        -> case coe v8 of
             C_valid'45'μ'45'wf_878 v15 v17
               -> coe
                    C_valid'45'μ'45'wf_878 v15
                    (coe
                       du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v15) (coe v4))
                       (coe v5) (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
        -> case coe v8 of
             C_valid'45'ν'45'wf_894 v15 v17
               -> coe
                    C_valid'45'ν'45'wf_894 v15
                    (coe
                       du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v15) (coe v4))
                       (coe v5) (coe v6) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v8 of
             C_valid'45'int'45'wf_906 v14
               -> coe
                    C_valid'45'int'45'wf_906
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
                       (coe v2) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v8 of
             C_valid'45'float'45'wf_918 v14
               -> coe
                    C_valid'45'float'45'wf_918
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
                       (coe v2) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v8 of
             C_valid'45'str'45'wf_930 v14
               -> coe
                    C_valid'45'str'45'wf_930
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
                       (coe v2) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v8 of
             C_valid'45'buffer'45'wf_942 v14
               -> coe
                    C_valid'45'buffer'45'wf_942
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
                       (coe v2) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_3050 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_fb''_3050 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21 ~v22
  = du_fb''_3050 v3 v11 v18
du_fb''_3050 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_fb''_3050 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_3052 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sb''_3052 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22
  = du_sb''_3052 v3 v12 v19
du_sb''_3052 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_sb''_3052 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3054 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3054 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_slb''_3054 v3 v8 v20
du_slb''_3054 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3054 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3056 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_fv''_3056 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9 v10 v11 ~v12 v13 ~v14
            ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22
  = du_fv''_3056 v0 v1 v3 v4 v6 v9 v10 v11 v13 v21
du_fv''_3056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_fv''_3056 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3058 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_sv''_3058 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 v12 ~v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22
  = du_sv''_3058 v0 v1 v3 v5 v7 v9 v10 v12 v14 v22
du_sv''_3058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_sv''_3058 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v7) (coe v5) (coe v6) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_3100 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_eb''_3100 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 ~v22
  = du_eb''_3100 v3 v13 v19
du_eb''_3100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_eb''_3100 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3102 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3102 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_slb''_3102 v3 v6 v20
du_slb''_3102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3102 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3104 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_BodyCorrect_756 -> T_ValidAtWF_530
d_ev''_3104 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 v11 ~v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22
  = du_ev''_3104 v0 v1 v3 v7 v8 v9 v11 v13 v14 v21
du_ev''_3104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_ev''_3104 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
      (coe v5) (coe v6) (coe v7) (coe v3) (coe v4) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3140 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_pb''_3140 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13 ~v14 v15 ~v16 ~v17
  = du_pb''_3140 v3 v10 v15
du_pb''_3140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_pb''_3140 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3142 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3142 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16 ~v17
  = du_slb''_3142 v3 v6 v16
du_slb''_3142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3142 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3144 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_3144 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 ~v16 v17
  = du_pv''_3144 v0 v1 v3 v4 v7 v8 v9 v10 v11 v17
du_pv''_3144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_3144 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3180 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_pb''_3180 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
            ~v13 ~v14 v15 ~v16 ~v17
  = du_pb''_3180 v3 v10 v15
du_pb''_3180 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_pb''_3180 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3182 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3182 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16 ~v17
  = du_slb''_3182 v3 v6 v16
du_slb''_3182 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3182 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_stack'45'alloc'45'advances_768
      (coe v0)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v1))
      (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3184 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_3184 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 ~v16 v17
  = du_pv''_3184 v0 v1 v3 v5 v7 v8 v9 v10 v11 v17
du_pv''_3184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_3184 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'alloc'45'advance_2996 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v7) (coe v4) (coe v5) (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-frontier-advance
d_validityWF'45'frontier'45'advance_3288 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'frontier'45'advance_3288 v0 v1 ~v2 v3 v4 v5 v6 v7
                                         v8 ~v9 v10 v11 v12
  = du_validityWF'45'frontier'45'advance_3288
      v0 v1 v3 v4 v5 v6 v7 v8 v10 v11 v12
du_validityWF'45'frontier'45'advance_3288 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'frontier'45'advance_3288 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v5) (coe seq (coe v10) (coe C_valid'45'unit'45'wf_766))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
               -> case coe v10 of
                    C_valid'45'pair'45'wf_792 v22 v23 v25 v26 v27 v30 v31 v32 v33 v34
                      -> coe
                           C_valid'45'pair'45'wf_792 v22 v23 v25 v26 v27
                           (coe du_fb''_3354 (coe v8) (coe v9) (coe v22) (coe v30))
                           (coe du_sb''_3356 (coe v8) (coe v9) (coe v23) (coe v31))
                           (coe du_slb''_3358 (coe v6) (coe v8) (coe v9) (coe v32))
                           (coe
                              du_fv''_3360 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                              (coe v13) (coe v7) (coe v8) (coe v9) (coe v22) (coe v25) (coe v33))
                           (coe
                              du_sv''_3362 (coe v0) (coe v1) (coe v2) (coe v3) (coe v12)
                              (coe v14) (coe v7) (coe v8) (coe v9) (coe v23) (coe v26) (coe v34))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
        -> case coe v10 of
             C_valid'45'inl'45'wf_842 v19 v21 v22 v25 v26 v27
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v28
                      -> coe
                           C_valid'45'inl'45'wf_842 v19 v21 v22
                           (coe du_pb''_3456 (coe v8) (coe v9) (coe v19) (coe v25))
                           (coe du_slb''_3458 (coe v6) (coe v8) (coe v9) (coe v26))
                           (coe
                              du_pv''_3460 (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v7)
                              (coe v8) (coe v9) (coe v28) (coe v19) (coe v21) (coe v27))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v19 v21 v22 v25 v26 v27
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v28
                      -> coe
                           C_valid'45'inr'45'wf_862 v19 v21 v22
                           (coe du_pb''_3502 (coe v8) (coe v9) (coe v19) (coe v25))
                           (coe du_slb''_3504 (coe v6) (coe v8) (coe v9) (coe v26))
                           (coe
                              du_pv''_3506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v7)
                              (coe v8) (coe v9) (coe v28) (coe v19) (coe v21) (coe v27))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
        -> case coe v10 of
             C_valid'45'closure'45'wf_822 v14 v17 v18 v20 v22 v24 v25 v26 v29 v30 v31 v32
               -> coe
                    C_valid'45'closure'45'wf_822 v14 v17 v18 v20 v22 v24 v25 v26
                    (coe du_eb''_3410 (coe v8) (coe v9) (coe v22) (coe v29))
                    (coe du_slb''_3412 (coe v6) (coe v8) (coe v9) (coe v30))
                    (coe
                       du_ev''_3414 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)
                       (coe v9) (coe v14) (coe v18) (coe v22) (coe v24) (coe v31))
                    v32
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v11
        -> case coe v10 of
             C_valid'45'μ'45'wf_878 v17 v19
               -> coe
                    C_valid'45'μ'45'wf_878 v17
                    (coe
                       du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v17) (coe v5))
                       (coe v6) (coe v7) (coe v8) (coe v9) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
        -> case coe v10 of
             C_valid'45'ν'45'wf_894 v17 v19
               -> coe
                    C_valid'45'ν'45'wf_894 v17
                    (coe
                       du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
                       (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v4))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v4)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v4))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v17) (coe v5))
                       (coe v6) (coe v7) (coe v8) (coe v9) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v10 of
             C_valid'45'int'45'wf_906 v16
               -> coe
                    C_valid'45'int'45'wf_906
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
                       (coe v8) (coe v9) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v10 of
             C_valid'45'float'45'wf_918 v16
               -> coe
                    C_valid'45'float'45'wf_918
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
                       (coe v8) (coe v9) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v10 of
             C_valid'45'str'45'wf_930 v16
               -> coe
                    C_valid'45'str'45'wf_930
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
                       (coe v8) (coe v9) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v10 of
             C_valid'45'buffer'45'wf_942 v16
               -> coe
                    C_valid'45'buffer'45'wf_942
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
                       (coe v8) (coe v9) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fb'
d_fb''_3354 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_fb''_3354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 ~v25
  = du_fb''_3354 v12 v13 v14 v21
du_fb''_3354 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_fb''_3354 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sb'
d_sb''_3356 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_sb''_3356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25
  = du_sb''_3356 v12 v13 v15 v22
du_sb''_3356 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_sb''_3356 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3358 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 v12
             v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25
  = du_slb''_3358 v9 v12 v13 v23
du_slb''_3358 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3358 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3360 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_fv''_3360 v0 v1 ~v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 v10 ~v11 v12 v13 v14
            ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_fv''_3360 v0 v1 v3 v4 v5 v7 v10 v12 v13 v14 v16 v24
du_fv''_3360 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_fv''_3360 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v6) (coe v7)
      (coe v8) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3362 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_sv''_3362 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 ~v11 v12 v13 ~v14
            v15 ~v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25
  = du_sv''_3362 v0 v1 v3 v4 v6 v8 v10 v12 v13 v15 v17 v25
du_sv''_3362 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_sv''_3362 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v9) (coe v6) (coe v7)
      (coe v8) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.eb'
d_eb''_3410 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_eb''_3410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 ~v23 ~v24 ~v25
  = du_eb''_3410 v10 v11 v16 v22
du_eb''_3410 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_eb''_3410 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3412 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24 ~v25
  = du_slb''_3412 v7 v10 v11 v23
du_slb''_3412 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3412 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_3414 ::
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_BodyCorrect_756 -> T_ValidAtWF_530
d_ev''_3414 v0 v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8 ~v9 v10 v11 v12 ~v13 v14
            ~v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_ev''_3414 v0 v1 v3 v4 v8 v10 v11 v12 v14 v16 v17 v24
du_ev''_3414 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_ev''_3414 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v7) (coe v8) (coe v9) (coe v4) (coe v5)
      (coe v6) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3456 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_pb''_3456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20
  = du_pb''_3456 v10 v11 v13 v18
du_pb''_3456 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_pb''_3456 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3458 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_slb''_3458 v7 v10 v11 v19
du_slb''_3458 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3458 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3460 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_3460 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 v10 v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_3460 v0 v1 v3 v4 v5 v8 v10 v11 v12 v13 v14 v20
du_pv''_3460 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_3460 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v5) (coe v6)
      (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pb'
d_pb''_3502 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_pb''_3502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20
  = du_pb''_3502 v10 v11 v13 v18
du_pb''_3502 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_pb''_3502 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.slb'
d_slb''_3504 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_slb''_3504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_slb''_3504 v7 v10 v11 v19
du_slb''_3504 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_slb''_3504 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.du_frontier'45'monotone_838
      (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v0))
      (coe v3)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_3506 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_3506 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 v8 ~v9 v10 v11 v12 v13 v14
            ~v15 ~v16 ~v17 ~v18 ~v19 v20
  = du_pv''_3506 v0 v1 v3 v4 v6 v8 v10 v11 v12 v13 v14 v20
du_pv''_3506 ::
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_3506 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v8) (coe v9) (coe v5) (coe v6)
      (coe v7) (coe v11)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-with-bf-transfer
d_validityWF'45'with'45'bf'45'transfer_3650 ::
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
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634) ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'with'45'bf'45'transfer_3650 ~v0 ~v1 ~v2 v3 v4 v5
                                            ~v6 ~v7 ~v8 v9 v10
  = du_validityWF'45'with'45'bf'45'transfer_3650 v3 v4 v5 v9 v10
du_validityWF'45'with'45'bf'45'transfer_3650 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634) ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'with'45'bf'45'transfer_3650 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v1) (coe seq (coe v4) (coe C_valid'45'unit'45'wf_766))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v4 of
                    C_valid'45'pair'45'wf_792 v16 v17 v19 v20 v21 v24 v25 v26 v27 v28
                      -> coe
                           C_valid'45'pair'45'wf_792 v16 v17 v19 v20 v21 (coe v3 v16 v24)
                           (coe v3 v17 v25)
                           (coe
                              v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                              v26)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3650 (coe v5) (coe v7)
                              (coe v16) (coe v3) (coe v27))
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3650 (coe v6) (coe v8)
                              (coe v17) (coe v3) (coe v28))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v5 v6
        -> case coe v4 of
             C_valid'45'inl'45'wf_842 v13 v15 v16 v19 v20 v21
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
                      -> coe
                           C_valid'45'inl'45'wf_842 v13 v15 v16 (coe v3 v13 v19)
                           (coe
                              v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                              v20)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3650 (coe v5) (coe v22)
                              (coe v13) (coe v3) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v13 v15 v16 v19 v20 v21
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
                      -> coe
                           C_valid'45'inr'45'wf_862 v13 v15 v16 (coe v3 v13 v19)
                           (coe
                              v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                              v20)
                           (coe
                              du_validityWF'45'with'45'bf'45'transfer_3650 (coe v6) (coe v22)
                              (coe v13) (coe v3) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v5 v6
        -> case coe v4 of
             C_valid'45'closure'45'wf_822 v8 v11 v12 v14 v16 v18 v19 v20 v23 v24 v25 v26
               -> coe
                    C_valid'45'closure'45'wf_822 v8 v11 v12 v14 v16 v18 v19 v20
                    (coe v3 v16 v23)
                    (coe
                       v3 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_sucLoc_84 (coe v2))
                       v24)
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3650 (coe v8) (coe v12)
                       (coe v16) (coe v3) (coe v25))
                    v26
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v5
        -> case coe v4 of
             C_valid'45'μ'45'wf_878 v11 v13
               -> coe
                    C_valid'45'μ'45'wf_878 v11
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3650
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
             C_valid'45'ν'45'wf_894 v11 v13
               -> coe
                    C_valid'45'ν'45'wf_894 v11
                    (coe
                       du_validityWF'45'with'45'bf'45'transfer_3650
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
             C_valid'45'int'45'wf_906 v10
               -> coe C_valid'45'int'45'wf_906 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v4 of
             C_valid'45'float'45'wf_918 v10
               -> coe C_valid'45'float'45'wf_918 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v4 of
             C_valid'45'str'45'wf_930 v10
               -> coe C_valid'45'str'45'wf_930 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v4 of
             C_valid'45'buffer'45'wf_942 v10
               -> coe C_valid'45'buffer'45'wf_942 (coe v3 v2 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved
d_validityWF'45'mem'45'preserved_3922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'mem'45'preserved_3922 v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8
                                      ~v9 ~v10 v11
  = du_validityWF'45'mem'45'preserved_3922 v0 v1 v3 v4 v5 v7 v8 v11
du_validityWF'45'mem'45'preserved_3922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'mem'45'preserved_3922 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe
             seq (coe v4) (coe seq (coe v7) (coe C_valid'45'unit'45'wf_766))
      MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v7 of
                    C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29 v30 v31
                      -> coe
                           C_valid'45'pair'45'wf_792 v19 v20 v22 v23 v24 v27 v28 v29
                           (coe
                              du_fv''_3988 (coe v0) (coe v1) (coe v2) (coe v8) (coe v10) (coe v5)
                              (coe v6) (coe v19) (coe v22) (coe v27) (coe v30))
                           (coe
                              du_sv''_3990 (coe v0) (coe v1) (coe v2) (coe v9) (coe v11) (coe v5)
                              (coe v6) (coe v20) (coe v23) (coe v28) (coe v31))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
        -> case coe v7 of
             C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25
                      -> coe
                           C_valid'45'inl'45'wf_842 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_4084 (coe v0) (coe v1) (coe v2) (coe v8) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v22) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25
                      -> coe
                           C_valid'45'inr'45'wf_862 v16 v18 v19 v22 v23
                           (coe
                              du_pv''_4128 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5) (coe v6)
                              (coe v25) (coe v16) (coe v18) (coe v22) (coe v24))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C__'8667'__24 v8 v9
        -> case coe v7 of
             C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26 v27 v28 v29
               -> coe
                    C_valid'45'closure'45'wf_822 v11 v14 v15 v17 v19 v21 v22 v23 v26
                    v27
                    (coe
                       du_ev''_4040 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6) (coe v11)
                       (coe v15) (coe v19) (coe v21) (coe v26) (coe v28))
                    v29
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
        -> case coe v7 of
             C_valid'45'μ'45'wf_878 v14 v16
               -> coe
                    C_valid'45'μ'45'wf_878 v14
                    (coe
                       du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
        -> case coe v7 of
             C_valid'45'ν'45'wf_894 v14 v16
               -> coe
                    C_valid'45'ν'45'wf_894 v14
                    (coe
                       du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v3)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v8) (coe v3))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v14) (coe v4))
                       (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> case coe v7 of
             C_valid'45'int'45'wf_906 v13 -> coe C_valid'45'int'45'wf_906 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> case coe v7 of
             C_valid'45'float'45'wf_918 v13
               -> coe C_valid'45'float'45'wf_918 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Str_34
        -> case coe v7 of
             C_valid'45'str'45'wf_930 v13 -> coe C_valid'45'str'45'wf_930 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_Buffer_36
        -> case coe v7 of
             C_valid'45'buffer'45'wf_942 v13
               -> coe C_valid'45'buffer'45'wf_942 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_3984 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_3984 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_3986 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_3986 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_3988 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_fv''_3988 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9 v10 ~v11 ~v12 v13
            ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22 v23 ~v24
  = du_fv''_3988 v0 v1 v3 v4 v6 v9 v10 v13 v15 v20 v23
du_fv''_3988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_fv''_3988 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_3990 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530 -> T_ValidAtWF_530
d_sv''_3990 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 ~v8 v9 v10 ~v11 ~v12 ~v13
            v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 v24
  = du_sv''_3990 v0 v1 v3 v5 v7 v9 v10 v14 v16 v21 v24
du_sv''_3990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_sv''_3990 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_4036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_4036 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_4038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_4038 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_BodyCorrect_756 -> T_ValidAtWF_530
d_ev''_4040 v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 ~v12 v13
            ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 v23 ~v24
  = du_ev''_4040 v0 v1 v3 v7 v8 v11 v13 v15 v16 v21 v23
du_ev''_4040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_ev''_4040 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
      (coe v5) (coe v6) (coe v3) (coe v4) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_4080 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4082 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_4084 v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 ~v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_4084 v0 v1 v3 v4 v7 v8 v11 v12 v13 v17 v19
du_pv''_4084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_4084 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny
d_tg''_4124 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4126 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_pv''_4128 v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 ~v9 ~v10 v11 v12 v13 ~v14
            ~v15 ~v16 v17 ~v18 v19
  = du_pv''_4128 v0 v1 v3 v5 v7 v8 v11 v12 v13 v17 v19
du_pv''_4128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_pv''_4128 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v6) (coe v4) (coe v5) (coe v10)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-excluding
d_validityWF'45'mem'45'preserved'45'excluding_4266 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'mem'45'preserved'45'excluding_4266 ~v0 ~v1 ~v2 ~v3
  = du_validityWF'45'mem'45'preserved'45'excluding_4266
du_validityWF'45'mem'45'preserved'45'excluding_4266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'mem'45'preserved'45'excluding_4266
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocInRegions
d_LocInRegions_4274 a0 a1 a2 a3 a4 a5 = ()
data T_LocInRegions_4274
  = C_loc'45'in'45'input_4284 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'fresh_4288 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                              MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_loc'45'in'45'anc_4294 AgdaAny | C_loc'45'in'45'heap_4298
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.LocsInRegions
d_LocsInRegions_4316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> Integer -> T_ValidAtWF_530 -> ()
d_LocsInRegions_4316 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.loc-mem-eq-from-regions
d_loc'45'mem'45'eq'45'from'45'regions_4486 ::
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
  T_LocInRegions_4274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_loc'45'mem'45'eq'45'from'45'regions_4486 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.μ-validity-in-regions-stub
d_μ'45'validity'45'in'45'regions'45'stub_4558
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\956-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.ν-validity-in-regions-stub
d_ν'45'validity'45'in'45'regions'45'stub_4580
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.\957-validity-in-regions-stub"
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions-strong
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
d_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612 v0
                                                                 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                                                                 v12 v13 ~v14 ~v15 ~v16 ~v17 v18 v19
  = du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v18 v19
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612 ::
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
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                                                                  v12 v13 v14
  = case coe v13 of
      C_valid'45'unit'45'wf_766 -> coe C_valid'45'unit'45'wf_766
      C_valid'45'pair'45'wf_792 v22 v23 v25 v26 v27 v30 v31 v32 v33 v34
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v35 v36
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                      -> case coe v14 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                             -> case coe v40 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                    -> case coe v42 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                           -> coe
                                                C_valid'45'pair'45'wf_792 v22 v23 v25 v26 v27 v30
                                                v31 v32
                                                (coe
                                                   du_fv''_4698 (coe v0) (coe v1) (coe v4) (coe v7)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v35) (coe v37) (coe v22) (coe v25) (coe v30)
                                                   (coe v33) (coe v43))
                                                (coe
                                                   du_sv''_4700 (coe v0) (coe v1) (coe v4) (coe v7)
                                                   (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                                   (coe v36) (coe v38) (coe v23) (coe v26) (coe v31)
                                                   (coe v34) (coe v44))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'closure'45'wf_822 v16 v19 v20 v22 v24 v26 v27 v28 v31 v32 v33 v34
        -> case coe v14 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
               -> case coe v36 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                      -> coe
                           C_valid'45'closure'45'wf_822 v16 v19 v20 v22 v24 v26 v27 v28 v31
                           v32
                           (coe
                              du_ev''_4772 (coe v0) (coe v1) (coe v4) (coe v7) (coe v8) (coe v9)
                              (coe v10) (coe v11) (coe v12) (coe v16) (coe v20) (coe v24)
                              (coe v26) (coe v31) (coe v33) (coe v38))
                           v34
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inl'45'wf_842 v21 v23 v24 v27 v28 v29
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v30 v31
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v32
                      -> case coe v14 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                             -> case coe v34 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                    -> coe
                                         C_valid'45'inl'45'wf_842 v21 v23 v24 v27 v28
                                         (coe
                                            du_pv''_4832 (coe v0) (coe v1) (coe v4) (coe v7)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v30) (coe v32) (coe v21) (coe v23) (coe v27)
                                            (coe v29) (coe v36))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'inr'45'wf_862 v21 v23 v24 v27 v28 v29
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v30 v31
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v32
                      -> case coe v14 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                             -> case coe v34 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                    -> coe
                                         C_valid'45'inr'45'wf_862 v21 v23 v24 v27 v28
                                         (coe
                                            du_pv''_4892 (coe v0) (coe v1) (coe v4) (coe v7)
                                            (coe v8) (coe v9) (coe v10) (coe v11) (coe v12)
                                            (coe v31) (coe v32) (coe v21) (coe v23) (coe v27)
                                            (coe v29) (coe v36))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'μ'45'wf_878 v20 v22
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v23
               -> coe
                    C_valid'45'μ'45'wf_878 v20
                    (coe
                       d_μ'45'validity'45'in'45'regions'45'stub_4558 v0 v1 v2 v4 v23 v20
                       v5 v6 v9 v10 v7 v8 v22)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'ν'45'wf_894 v20 v22
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v23
               -> coe
                    C_valid'45'ν'45'wf_894 v20
                    (coe
                       d_ν'45'validity'45'in'45'regions'45'stub_4580 v0 v1 v2 v4 v23 v20
                       v5 v6 v9 v10 v7 v8 v22)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_valid'45'int'45'wf_906 v20 -> coe C_valid'45'int'45'wf_906 v20
      C_valid'45'float'45'wf_918 v20
        -> coe C_valid'45'float'45'wf_918 v20
      C_valid'45'str'45'wf_930 v20 -> coe C_valid'45'str'45'wf_930 v20
      C_valid'45'buffer'45'wf_942 v20
        -> coe C_valid'45'buffer'45'wf_942 v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pl-eq
d_pl'45'eq_4690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pl'45'eq_4690 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.spl-eq
d_spl'45'eq_4692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_spl'45'eq_4692 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fp'
d_fp''_4694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fp''_4694 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sp'
d_sp''_4696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp''_4696 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.fv'
d_fv''_4698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 -> AgdaAny -> AgdaAny -> T_ValidAtWF_530
d_fv''_4698 v0 v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 v16 ~v17 v18 ~v19 v20 ~v21 v22 ~v23 ~v24 ~v25 ~v26 v27 ~v28
            ~v29 v30 ~v31 ~v32 ~v33 v34 ~v35
  = du_fv''_4698
      v0 v1 v3 v5 v6 v7 v8 v10 v11 v16 v18 v20 v22 v27 v30 v34
du_fv''_4698 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
du_fv''_4698 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612
      (coe v0) (coe v1) (coe v12) (coe v9) (coe v2) (coe v10) (coe v11)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
      (coe v15)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sv'
d_sv''_4700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 -> AgdaAny -> AgdaAny -> T_ValidAtWF_530
d_sv''_4700 v0 v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 ~v16 v17 ~v18 v19 ~v20 v21 ~v22 v23 ~v24 ~v25 ~v26 ~v27 v28
            ~v29 ~v30 v31 ~v32 ~v33 ~v34 v35
  = du_sv''_4700
      v0 v1 v3 v5 v6 v7 v8 v10 v11 v17 v19 v21 v23 v28 v31 v35
du_sv''_4700 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
du_sv''_4700 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612
      (coe v0) (coe v1) (coe v12) (coe v9) (coe v2) (coe v10) (coe v11)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
      (coe v15)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cl-eq
d_cl'45'eq_4764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cl'45'eq_4764 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.scl-eq
d_scl'45'eq_4766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scl'45'eq_4766 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ep'
d_ep''_4768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ep''_4768 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.cp'
d_cp''_4770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cp''_4770 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.ev'
d_ev''_4772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_BodyCorrect_756 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 -> AgdaAny -> T_ValidAtWF_530
d_ev''_4772 v0 v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 v16 ~v17 ~v18 ~v19 v20 ~v21 v22 v23 ~v24 ~v25 ~v26 ~v27 v28
            ~v29 v30 ~v31 ~v32 ~v33 v34
  = du_ev''_4772
      v0 v1 v3 v5 v6 v7 v8 v10 v11 v16 v20 v22 v23 v28 v30 v34
du_ev''_4772 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
du_ev''_4772 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612
      (coe v0) (coe v1) (coe v12) (coe v9) (coe v2) (coe v10) (coe v11)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
      (coe v15)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 -> T_LocInRegions_4274 -> AgdaAny -> AgdaAny
d_tg''_4826 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_4828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_4828 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4830 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 -> AgdaAny -> T_ValidAtWF_530
d_pv''_4832 v0 v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 v16 ~v17 v18 v19 v20 ~v21 ~v22 ~v23 v24 ~v25 v26 ~v27 ~v28 v29
  = du_pv''_4832
      v0 v1 v3 v5 v6 v7 v8 v10 v11 v16 v18 v19 v20 v24 v26 v29
du_pv''_4832 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
du_pv''_4832 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612
      (coe v0) (coe v1) (coe v12) (coe v9) (coe v2) (coe v10) (coe v11)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
      (coe v15)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.tg'
d_tg''_4886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 -> T_LocInRegions_4274 -> AgdaAny -> AgdaAny
d_tg''_4886 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.sl-eq
d_sl'45'eq_4888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sl'45'eq_4888 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pp'
d_pp''_4890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pp''_4890 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.pv'
d_pv''_4892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 ->
  T_LocInRegions_4274 ->
  T_LocInRegions_4274 -> AgdaAny -> T_ValidAtWF_530
d_pv''_4892 v0 v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12 ~v13 ~v14
            ~v15 ~v16 v17 v18 v19 v20 ~v21 ~v22 ~v23 v24 ~v25 v26 ~v27 ~v28 v29
  = du_pv''_4892
      v0 v1 v3 v5 v6 v7 v8 v10 v11 v17 v18 v19 v20 v24 v26 v29
du_pv''_4892 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny -> T_ValidAtWF_530
du_pv''_4892 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  = coe
      du_validityWF'45'mem'45'preserved'45'in'45'regions'45'strong_4612
      (coe v0) (coe v1) (coe v12) (coe v9) (coe v2) (coe v10) (coe v11)
      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
      (coe v15)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-mem-preserved-in-regions
d_validityWF'45'mem'45'preserved'45'in'45'regions_5050 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'mem'45'preserved'45'in'45'regions_5050 ~v0 ~v1 ~v2
                                                       ~v3
  = du_validityWF'45'mem'45'preserved'45'in'45'regions_5050
du_validityWF'45'mem'45'preserved'45'in'45'regions_5050 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
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
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'mem'45'preserved'45'in'45'regions_5050
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.reclaim-alloc
d_reclaim'45'alloc_5056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_reclaim'45'alloc_5056 ~v0 ~v1 v2 v3
  = du_reclaim'45'alloc_5056 v2 v3
du_reclaim'45'alloc_5056 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_reclaim'45'alloc_5056 v0 v1
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
d_reclaim'45'preserves'45'frontier_5070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_reclaim'45'preserves'45'frontier_5070 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reclaim'45'preserves'45'frontier_5070 v4 v5 v6
du_reclaim'45'preserves'45'frontier_5070 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_reclaim'45'preserves'45'frontier_5070 v0 v1 v2
  = coe
      du_stack'45'alloc'45'advances''_5094 (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.stack-alloc-advances'
d_stack'45'alloc'45'advances''_5094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_stack'45'alloc'45'advances''_5094 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10 v11
  = du_stack'45'alloc'45'advances''_5094 v9 v10 v11
du_stack'45'alloc'45'advances''_5094 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_stack'45'alloc'45'advances''_5094 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_642 v8
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_642
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v8) (coe v0))
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_652 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_652 v7
                    v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656 v5
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-reclaim
d_validityWF'45'reclaim_5154 ::
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
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
d_validityWF'45'reclaim_5154 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 ~v10
                             v11
  = du_validityWF'45'reclaim_5154 v0 v1 v3 v4 v5 v6 v7 v8 v9 v11
du_validityWF'45'reclaim_5154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'reclaim_5154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_validityWF'45'frontier'45'advance_3288 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v2)))
      (coe du_reclaim'45'alloc_5056 (coe v2) (coe v7)) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v8)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v2)))
      (coe v9)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved-at
d_derive'45'mem'45'preserved'45'at_5188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved'45'at_5188 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef._.k<start
d_k'60'start_5216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'start_5216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                  v12
  = du_k'60'start_5216 v11 v12
du_k'60'start_5216 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'start_5216 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v0) (coe v1)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.derive-mem-preserved
d_derive'45'mem'45'preserved_5260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derive'45'mem'45'preserved_5260 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.validityWF-trace-preserves
d_validityWF'45'trace'45'preserves_5294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  T_ValidAtWF_530 -> AgdaAny -> AgdaAny -> T_ValidAtWF_530
d_validityWF'45'trace'45'preserves_5294 v0 v1 ~v2 v3 v4 v5 v6 ~v7
                                        v8 ~v9 v10 ~v11 ~v12
  = du_validityWF'45'trace'45'preserves_5294 v0 v1 v3 v4 v5 v6 v8 v10
du_validityWF'45'trace'45'preserves_5294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_ValidAtWF_530 -> T_ValidAtWF_530
du_validityWF'45'trace'45'preserves_5294 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_validityWF'45'mem'45'preserved_3922 (coe v0) (coe v1) (coe v3)
      (coe v2) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2768 (coe v0)
            (coe v4) (coe v6) (coe v3)))
      (coe v7)
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.irresult-mem-preserved
d_irresult'45'mem'45'preserved_5332 ::
  T_IRResultAWF_686 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irresult'45'mem'45'preserved_5332 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-from-tnhw
d_mem'45'preserved'45'from'45'tnhw_5344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'from'45'tnhw_5344 = erased
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.before-frontier-monotone
d_before'45'frontier'45'monotone_5376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
d_before'45'frontier'45'monotone_5376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                      v8
  = du_before'45'frontier'45'monotone_5376 v6 v7 v8
du_before'45'frontier'45'monotone_5376 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
du_before'45'frontier'45'monotone_5376 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_642 v6
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'before_642
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v6) (coe v0))
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_652 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_stack'45'ancestor_652 v5
             v6 v7 v8
      MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656 v4
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Allocation.C_heap'45'before_656
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ClosureWellFormed.ClosureWellFormedDef.mem-preserved-compose
d_mem'45'preserved'45'compose_5458 ::
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
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'preserved'45'compose_5458 = erased
