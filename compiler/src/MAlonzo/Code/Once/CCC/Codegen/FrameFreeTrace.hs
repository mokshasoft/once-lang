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

module MAlonzo.Code.Once.CCC.Codegen.FrameFreeTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.FrameFreeTrace._.cata-body
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
-- Once.CCC.Codegen.FrameFreeTrace._.cata-call
d_cata'45'call_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'call_16 ~v0 = du_cata'45'call_16
du_cata'45'call_16 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_cata'45'call_16
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
-- Once.CCC.Codegen.FrameFreeTrace._.cata-call-setup
d_cata'45'call'45'setup_18 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'call'45'setup_18 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-dispatch
d_cata'45'dispatch_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'dispatch_356
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-nat-I₁
d_cata'45'nat'45'I'8321'_22 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'nat'45'I'8321'_22 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8321'_74
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-nat-I₂
d_cata'45'nat'45'I'8322'_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'nat'45'I'8322'_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8322'_80
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-nat-I₃
d_cata'45'nat'45'I'8323'_26 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'nat'45'I'8323'_26 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8323'_86
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-trace-branching
d_cata'45'trace'45'branching_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_30 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'branching_334
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-trace-const
d_cata'45'trace'45'const_32 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'const_32 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'const_346
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-trace-linear
d_cata'45'trace'45'linear_34 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'linear_34 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'linear_140
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cata-trace-nat
d_cata'45'trace'45'nat_36 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'nat_36 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'trace'45'nat_114
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.ir-to-trace
d_ir'45'to'45'trace_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace_40 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_732
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.ir-to-trace'
d_ir'45'to'45'trace''_42 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_42 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_44 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_ir'45'to'45'trace'45'at'45'frontier_44 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace'45'at'45'frontier_740
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.pop2
d_pop2_48 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_pop2_48 ~v0 = du_pop2_48
du_pop2_48 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_pop2_48
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_pop2_176
-- Once.CCC.Codegen.FrameFreeTrace._.push2
d_push2_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_push2_50 ~v0 = du_push2_50
du_push2_50 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_push2_50
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
-- Once.CCC.Codegen.FrameFreeTrace._.rebuild-walk
d_rebuild'45'walk_52 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_rebuild'45'walk_52 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
      (coe v0) v1 v4 v5 v6
-- Once.CCC.Codegen.FrameFreeTrace._.visit-walk
d_visit'45'walk_62 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_visit'45'walk_62 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
      (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.wrap-sum
d_wrap'45'sum_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_wrap'45'sum_64 ~v0 = du_wrap'45'sum_64
du_wrap'45'sum_64 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_wrap'45'sum_64
  = coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_184
-- Once.CCC.Codegen.FrameFreeTrace.trace-of
d_trace'45'of_76 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_trace'45'of_76 ~v0 v1 = du_trace'45'of_76 v1
du_trace'45'of_76 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_trace'45'of_76 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FrameFreeTrace.cata-trace-of
d_cata'45'trace'45'of_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
d_cata'45'trace'45'of_80 ~v0 v1 = du_cata'45'trace'45'of_80 v1
du_cata'45'trace'45'of_80 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218]
du_cata'45'trace'45'of_80 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FrameFreeTrace.FrameFreeTrace
d_FrameFreeTrace_84 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] -> ()
d_FrameFreeTrace_84 = erased
-- Once.CCC.Codegen.FrameFreeTrace.push2-ff
d_push2'45'ff_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_push2'45'ff_92 ~v0 ~v1 ~v2 ~v3 = du_push2'45'ff_92
du_push2'45'ff_92 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_push2'45'ff_92
  = coe
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
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.FrameFreeTrace.pop2-ff
d_pop2'45'ff_102 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_pop2'45'ff_102 ~v0 ~v1 = du_pop2'45'ff_102
du_pop2'45'ff_102 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_pop2'45'ff_102
  = coe
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
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.FrameFreeTrace.wrap-sum-ff
d_wrap'45'sum'45'ff_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_wrap'45'sum'45'ff_110 ~v0 ~v1 ~v2 = du_wrap'45'sum'45'ff_110
du_wrap'45'sum'45'ff_110 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_wrap'45'sum'45'ff_110
  = coe
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
-- Once.CCC.Codegen.FrameFreeTrace.visit-walk-ff
d_visit'45'walk'45'ff_128 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_visit'45'walk'45'ff_128 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Type.C_K_110 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.Type.C_Id_112
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe du_push2'45'ff_92)
      MAlonzo.Code.Once.Type.C__'8853'__114 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7)))
                      (coe v6)))
                (coe
                   d_visit'45'walk'45'ff_128 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v8) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7)))
                      (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
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
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         d_visit'45'walk'45'ff_128 (coe v0) (coe v1) (coe v2) (coe v3)
                         (coe v7) (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
      MAlonzo.Code.Once.Type.C__'8855'__116 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
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
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7))
                      (coe v6)))
                (coe
                   d_visit'45'walk'45'ff_128 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v8) (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v7))
                      (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                   (coe
                      d_visit'45'walk'45'ff_128 (coe v0) (coe v1) (coe v2) (coe v3)
                      (coe v7) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FrameFreeTrace.rebuild-walk-ff
d_rebuild'45'walk'45'ff_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_rebuild'45'walk'45'ff_190 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_rebuild'45'walk'45'ff_190 v0 v1 v4 v5 v6
du_rebuild'45'walk'45'ff_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_rebuild'45'walk'45'ff_190 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_K_110 v5
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.Type.C_Id_112 -> coe du_pop2'45'ff_102
      MAlonzo.Code.Once.Type.C__'8853'__114 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                   (coe v0) (coe v1) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v5)))
                      (coe v4)))
                (coe
                   du_rebuild'45'walk'45'ff_190 (coe v0) (coe v1) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe
                         addInt (coe (2 :: Integer))
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v5)))
                      (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_184
                      (coe (1 :: Integer)) (coe v3))
                   (coe du_wrap'45'sum'45'ff_110)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
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
                                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                         (coe
                            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                            (coe v0) (coe v1) (coe v5)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            du_rebuild'45'walk'45'ff_190 (coe v0) (coe v1) (coe v5)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_wrap'45'sum_184
                               (coe (0 :: Integer)) (coe v3))
                            (coe du_wrap'45'sum'45'ff_110)
                            (coe
                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))
      MAlonzo.Code.Once.Type.C__'8855'__116 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
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
                         (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                   (coe v0) (coe v1) (coe v5)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                (coe
                   du_rebuild'45'walk'45'ff_190 (coe v0) (coe v1) (coe v5)
                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2238
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
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
                               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                         (coe v0) (coe v1) (coe v6)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v5))
                            (coe v4)))
                      (coe
                         du_rebuild'45'walk'45'ff_190 (coe v0) (coe v1) (coe v6)
                         (coe addInt (coe (4 :: Integer)) (coe v3))
                         (coe
                            addInt
                            (coe MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v5))
                            (coe v4)))
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
                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FrameFreeTrace.cata-body-ff
d_cata'45'body'45'ff_248 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'body'45'ff_248 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_cata'45'body'45'ff_248 v4 v5
du_cata'45'body'45'ff_248 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'body'45'ff_248 v0 v1
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
-- Once.CCC.Codegen.FrameFreeTrace.cata-setup-ff
d_cata'45'setup'45'ff_266 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'setup'45'ff_266 ~v0 ~v1 ~v2 ~v3
  = du_cata'45'setup'45'ff_266
du_cata'45'setup'45'ff_266 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'setup'45'ff_266
  = coe
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
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
-- Once.CCC.Codegen.FrameFreeTrace.cata-call-ff
d_cata'45'call'45'ff_278 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'call'45'ff_278 ~v0 ~v1 ~v2 = du_cata'45'call'45'ff_278
du_cata'45'call'45'ff_278 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'call'45'ff_278
  = coe
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
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.CCC.Codegen.FrameFreeTrace.nat-I₁-ff
d_nat'45'I'8321''45'ff_288 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_nat'45'I'8321''45'ff_288 v0 v1 v2
  = coe
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
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (2 :: Integer)) (coe v2)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                             (coe addInt (coe (2 :: Integer)) (coe v2)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe v2))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                         (coe v0)
                                                         (coe
                                                            addInt (coe (1 :: Integer)) (coe v2)))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
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
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))
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
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                 (coe v1))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                       (coe addInt (coe (1 :: Integer)) (coe v1)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                             (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                         (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
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
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.CCC.Codegen.FrameFreeTrace.nat-I₂-ff
d_nat'45'I'8322''45'ff_298 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_nat'45'I'8322''45'ff_298 ~v0 v1 ~v2
  = du_nat'45'I'8322''45'ff_298 v1
du_nat'45'I'8322''45'ff_298 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_nat'45'I'8322''45'ff_298 v0
  = coe
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
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                        (coe v0))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                              (coe addInt (coe (1 :: Integer)) (coe v0)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                    (coe (1 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                          (coe v0))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                (coe addInt (coe (1 :: Integer)) (coe v0)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
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
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.FrameFreeTrace.nat-I₃-ff
d_nat'45'I'8323''45'ff_306 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_nat'45'I'8323''45'ff_306 ~v0 ~v1 = du_nat'45'I'8323''45'ff_306
du_nat'45'I'8323''45'ff_306 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_nat'45'I'8323''45'ff_306
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.FrameFreeTrace.cata-nat-ff
d_cata'45'nat'45'ff_318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'nat'45'ff_318 v0 ~v1 v2 v3 v4 v5
  = du_cata'45'nat'45'ff_318 v0 v2 v3 v4 v5
du_cata'45'nat'45'ff_318 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'nat'45'ff_318 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
         (coe v0) (coe du_cl_338 (coe v1)) (coe du_k_340 (coe v1))
         (coe du_bodyL_334 (coe v2)))
      (coe du_cata'45'setup'45'ff_266)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8321'_74
            (coe v0) (coe v1) (coe v2))
         (coe d_nat'45'I'8321''45'ff_288 (coe v0) (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
               (coe du_cl_338 (coe v1)) (coe du_k_340 (coe v1)))
            (coe du_cata'45'call'45'ff_278)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8322'_80
                  (coe v0) (coe v1) (coe v2))
               (coe du_nat'45'I'8322''45'ff_298 (coe v1))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
                     (coe du_cl_338 (coe v1)) (coe du_k_340 (coe v1)))
                  (coe du_cata'45'call'45'ff_278)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'nat'45'I'8323'_86
                        (coe v0) (coe v2))
                     (coe du_nat'45'I'8323''45'ff_306)
                     (coe du_cata'45'body'45'ff_248 (coe v3) (coe v4)))))))
-- Once.CCC.Codegen.FrameFreeTrace._.bodyL
d_bodyL_334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_bodyL_334 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_bodyL_334 v3
du_bodyL_334 :: Integer -> Integer
du_bodyL_334 v0 = coe addInt (coe (6 :: Integer)) (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.endL
d_endL_336 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_endL_336 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_endL_336 v3
du_endL_336 :: Integer -> Integer
du_endL_336 v0 = coe addInt (coe (7 :: Integer)) (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.cl
d_cl_338 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_cl_338 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_cl_338 v2
du_cl_338 :: Integer -> Integer
du_cl_338 v0 = coe addInt (coe (2 :: Integer)) (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace._.k
d_k_340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_k_340 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_k_340 v2
du_k_340 :: Integer -> Integer
du_k_340 v0 = coe addInt (coe (3 :: Integer)) (coe v0)
-- Once.CCC.Codegen.FrameFreeTrace.cata-const-ff
d_cata'45'const'45'ff_350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'const'45'ff_350 v0 ~v1 v2 v3 v4 v5
  = du_cata'45'const'45'ff_350 v0 v2 v3 v4 v5
du_cata'45'const'45'ff_350 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'const'45'ff_350 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
         (coe v0) (coe v1) (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe v2))
      (coe du_cata'45'setup'45'ff_266)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
            (coe v1) (coe addInt (coe (1 :: Integer)) (coe v1)))
         (coe du_cata'45'call'45'ff_278)
         (coe du_cata'45'body'45'ff_248 (coe v3) (coe v4)))
-- Once.CCC.Codegen.FrameFreeTrace.cata-linear-ff
d_cata'45'linear'45'ff_370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'linear'45'ff_370 v0 ~v1 v2 v3 v4 v5
  = du_cata'45'linear'45'ff_370 v0 v2 v3 v4 v5
du_cata'45'linear'45'ff_370 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'linear'45'ff_370 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
         (coe v0) (coe addInt (coe (6 :: Integer)) (coe v1))
         (coe addInt (coe (7 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v2)))
      (coe du_cata'45'setup'45'ff_266)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                  (coe (0 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (3 :: Integer)) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v2))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v2)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (5 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (2 :: Integer)) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                      (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v1)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                  (coe
                                                                     addInt (coe (3 :: Integer))
                                                                     (coe v1)))
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
                                                                           (coe (1 :: Integer))
                                                                           (coe v1)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                           (coe
                                                                              addInt
                                                                              (coe (3 :: Integer))
                                                                              (coe v1)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v1)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                          (coe v0)
                                                                                          (coe
                                                                                             v2))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252
                                                                                             (coe
                                                                                                v0)
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v2)))))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))))
         (coe du_lin'45'I'8321'_386)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
               (coe addInt (coe (6 :: Integer)) (coe v1))
               (coe addInt (coe (7 :: Integer)) (coe v1)))
            (coe du_cata'45'call'45'ff_278)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                           (coe addInt (coe (2 :: Integer)) (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2210
                           (coe
                              MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                              (coe addInt (coe (3 :: Integer)) (coe v2)))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (4 :: Integer)) (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (3 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                       (coe addInt (coe (5 :: Integer)) (coe v1)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                             (coe addInt (coe (3 :: Integer)) (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                (coe (2 :: Integer)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                   (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                         (coe addInt (coe (5 :: Integer)) (coe v1)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                               (coe
                                                                  addInt (coe (4 :: Integer))
                                                                  (coe v1)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                                                                     (coe (2 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                                        (coe v1))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                                                              (coe (1 :: Integer)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v1)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2234)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                                                          (coe v1))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
               (coe du_lin'45'I'8322'_388)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
                     (coe addInt (coe (6 :: Integer)) (coe v1))
                     (coe addInt (coe (7 :: Integer)) (coe v1)))
                  (coe du_cata'45'call'45'ff_278)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2284
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v2)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (3 :: Integer)) (coe v2)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                     (coe du_lin'45'I'8323'_390)
                     (coe du_cata'45'body'45'ff_248 (coe v3) (coe v4)))))))
-- Once.CCC.Codegen.FrameFreeTrace._.lin-I₁
d_lin'45'I'8321'_386 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lin'45'I'8321'_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_lin'45'I'8321'_386
du_lin'45'I'8321'_386 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lin'45'I'8321'_386
  = coe
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
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))))))))))))))
-- Once.CCC.Codegen.FrameFreeTrace._.lin-I₂
d_lin'45'I'8322'_388 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lin'45'I'8322'_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_lin'45'I'8322'_388
du_lin'45'I'8322'_388 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lin'45'I'8322'_388
  = coe
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
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))))))))))
-- Once.CCC.Codegen.FrameFreeTrace._.lin-I₃
d_lin'45'I'8323'_390 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lin'45'I'8323'_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_lin'45'I'8323'_390
du_lin'45'I'8323'_390 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lin'45'I'8323'_390
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
-- Once.CCC.Codegen.FrameFreeTrace.cata-branching-ff
d_cata'45'branching'45'ff_402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'branching'45'ff_402 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'branching'45'ff_402 v0 v1 v3 v4 v5 v6
du_cata'45'branching'45'ff_402 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'branching'45'ff_402 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_cata'45'call'45'setup_100
         (coe v0) (coe du_cl_422 (coe v1) (coe v2))
         (coe addInt (coe (1 :: Integer)) (coe du_cl_422 (coe v1) (coe v2)))
         (coe du_bodyL_420 (coe v1) (coe v3)))
      (coe du_cata'45'setup'45'ff_266)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (3 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                        (coe (2 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                           (coe addInt (coe (6 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                                 (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (2 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe addInt (coe (6 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                         (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166 (coe v2)
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                           (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                           (coe v2))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                       (coe v2))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (3 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
                        (coe addInt (coe (1 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                              (coe addInt (coe (3 :: Integer)) (coe v2)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                              (coe v0) (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
                              (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                              (coe addInt (coe (7 :: Integer)) (coe v2))
                              (coe addInt (coe (4 :: Integer)) (coe v3)))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                             (coe addInt (coe (1 :: Integer)) (coe v3)))))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                             (coe addInt (coe (2 :: Integer)) (coe v3)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                          (coe addInt (coe (1 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                      (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                                       (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                       (coe addInt (coe (7 :: Integer)) (coe v2))
                                       (coe
                                          addInt
                                          (coe
                                             addInt (coe (4 :: Integer))
                                             (coe
                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                                (coe v1)))
                                          (coe v3)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
         (coe du_I'8321'_424 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'call_108
               (coe du_cl_422 (coe v1) (coe v2))
               (coe
                  addInt (coe (1 :: Integer)) (coe du_cl_422 (coe v1) (coe v2))))
            (coe du_cata'45'call'45'ff_278)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
                     (coe addInt (coe (2 :: Integer)) (coe v2))
                     (coe addInt (coe (4 :: Integer)) (coe v2))
                     (coe addInt (coe (5 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                    (coe addInt (coe (3 :: Integer)) (coe v3)))))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                           (coe addInt (coe (2 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
               (coe du_I'8322'_426 (coe v0) (coe v2) (coe v3))
               (coe du_cata'45'body'45'ff_248 (coe v4) (coe v5)))))
-- Once.CCC.Codegen.FrameFreeTrace._.bodyL
d_bodyL_420 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_bodyL_420 ~v0 v1 ~v2 ~v3 v4 ~v5 ~v6 = du_bodyL_420 v1 v4
du_bodyL_420 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_bodyL_420 v0 v1
  = coe
      addInt
      (coe
         addInt
         (coe
            addInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190 (coe v0)))
      (coe v1)
-- Once.CCC.Codegen.FrameFreeTrace._.cl
d_cl_422 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> Integer
d_cl_422 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_cl_422 v1 v3
du_cl_422 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer -> Integer
du_cl_422 v0 v1
  = coe
      addInt
      (coe
         addInt (coe (11 :: Integer))
         (coe
            mulInt (coe (4 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_fsize_150 (coe v0))))
      (coe v1)
-- Once.CCC.Codegen.FrameFreeTrace._.I₁
d_I'8321'_424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8321'_424 v0 v1 ~v2 v3 v4 ~v5 ~v6 = du_I'8321'_424 v0 v1 v3 v4
du_I'8321'_424 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8321'_424 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2220)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2280
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2276
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2232)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
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
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166 (coe v2)
            (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe du_push2'45'ff_92)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
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
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
               (coe
                  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
                  (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe du_push2'45'ff_92)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_visit'45'walk_210
                        (coe v0) (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        d_visit'45'walk'45'ff_128 (coe v0) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2228
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2230
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2224)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
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
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_rebuild'45'walk_270
                                 (coe v0) (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                          (coe v1)))
                                    (coe v3)))
                              (coe
                                 du_rebuild'45'walk'45'ff_190 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe
                                       addInt (coe (4 :: Integer))
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_lsize_190
                                          (coe v1)))
                                    (coe v3)))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
-- Once.CCC.Codegen.FrameFreeTrace._.I₂
d_I'8322'_426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_I'8322'_426 v0 ~v1 ~v2 v3 v4 ~v5 ~v6 = du_I'8322'_426 v0 v3 v4
du_I'8322'_426 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_I'8322'_426 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_push2_166
         (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe du_push2'45'ff_92)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                     (coe addInt (coe (2 :: Integer)) (coe v2)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                     (coe
                        MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                        (coe addInt (coe (3 :: Integer)) (coe v2)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
-- Once.CCC.Codegen.FrameFreeTrace.cata-dispatch-ff
d_cata'45'dispatch'45'ff_438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cata'45'dispatch'45'ff_438 v0 v1 ~v2 v3 v4 v5 v6
  = du_cata'45'dispatch'45'ff_438 v0 v1 v3 v4 v5 v6
du_cata'45'dispatch'45'ff_438 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.Codegen.IRToTrace.T_CataStrategy_20 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cata'45'dispatch'45'ff_438 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'const_22
        -> coe
             du_cata'45'const'45'ff_350 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'nat_24
        -> coe
             du_cata'45'nat'45'ff_318 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'linear_26
        -> coe
             du_cata'45'linear'45'ff_370 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.C_strat'45'branching_28 v6
        -> coe
             du_cata'45'branching'45'ff_402 (coe v0) (coe v6) (coe v2) (coe v3)
             (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FrameFreeTrace.frame-free-trace'
d_frame'45'free'45'trace''_494 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_frame'45'free'45'trace''_494 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C__'8728'__30 v8 v10 v11
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe
                       du_trace'45'of_76
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                          (coe v0) (coe v1) (coe v8) (coe v5) (coe v6) (coe v11)))
                    (coe
                       d_frame'45'free'45'trace''_494 (coe v0) (coe v1) (coe v8) (coe v11)
                       (coe v12) (coe v5) (coe v6))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (d_frame'45'free'45'trace''_494
                          (coe v0) (coe v8) (coe v2) (coe v10) (coe v13)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                (coe v0) (coe v1) (coe v8) (coe v5) (coe v6) (coe v11)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                   (coe v0) (coe v1) (coe v8) (coe v5) (coe v6) (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v10 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v13 v14
               -> coe
                    seq (coe v12)
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                         -> case coe v16 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                -> coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                           (coe
                                              du_trace'45'of_76
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                 (coe v0) (coe v1) (coe v13)
                                                 (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6)
                                                 (coe v10)))
                                           (coe
                                              d_frame'45'free'45'trace''_494 (coe v0) (coe v1)
                                              (coe v13) (coe v10) (coe v17)
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
                                                       du_trace'45'of_76
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                          (coe v0) (coe v1) (coe v14)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                                (coe v0) (coe v1) (coe v13)
                                                                (coe
                                                                   addInt (coe (4 :: Integer))
                                                                   (coe v5))
                                                                (coe v6) (coe v10)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                                   (coe v0) (coe v1) (coe v13)
                                                                   (coe
                                                                      addInt (coe (4 :: Integer))
                                                                      (coe v5))
                                                                   (coe v6) (coe v10))))
                                                          (coe v11)))
                                                    (coe
                                                       d_frame'45'free'45'trace''_494 (coe v0)
                                                       (coe v1) (coe v14) (coe v11) (coe v18)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                             (coe v0) (coe v1) (coe v13)
                                                             (coe
                                                                addInt (coe (4 :: Integer))
                                                                (coe v5))
                                                             (coe v6) (coe v10)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                                (coe v0) (coe v1) (coe v13)
                                                                (coe
                                                                   addInt (coe (4 :: Integer))
                                                                   (coe v5))
                                                                (coe v6) (coe v10)))))
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
                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_inl_56 v9
        -> coe
             seq (coe v9)
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
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
      MAlonzo.Code.Once.IR.C_inr_62 v9
        -> coe
             seq (coe v9)
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
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
      MAlonzo.Code.Once.IR.C_case_70 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2212
                                    (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0) (coe v6))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe
                                 du_trace'45'of_76
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                    (coe v0) (coe v13) (coe v2)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v12) (coe v2) (coe v5)
                                          (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                             (coe v0) (coe v12) (coe v2) (coe v5)
                                             (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10))))
                                    (coe v11)))
                              (coe
                                 d_frame'45'free'45'trace''_494 (coe v0) (coe v13) (coe v2)
                                 (coe v11) (coe v15)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                       (coe v0) (coe v12) (coe v2) (coe v5)
                                       (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v12) (coe v2) (coe v5)
                                          (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2208
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                             (coe addInt (coe (1 :: Integer)) (coe v6)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2286
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2206
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_252 (coe v0)
                                                (coe v6))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2226)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2222)
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
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
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                    (coe
                                       du_trace'45'of_76
                                       (coe
                                          MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                          (coe v0) (coe v12) (coe v2) (coe v5)
                                          (coe addInt (coe (2 :: Integer)) (coe v6)) (coe v10)))
                                    (coe
                                       d_frame'45'free'45'trace''_494 (coe v0) (coe v12) (coe v2)
                                       (coe v10) (coe v14) (coe v5)
                                       (coe addInt (coe (2 :: Integer)) (coe v6)))
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_curry_86 v10 v11
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v12 v13
               -> coe
                    seq (coe v11)
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
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
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                  (coe
                                                                     du_trace'45'of_76
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                                                        (coe v0)
                                                                        (coe
                                                                           MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                           (coe v1) (coe v12))
                                                                        (coe v13)
                                                                        (coe (0 :: Integer))
                                                                        (coe
                                                                           addInt
                                                                           (coe (2 :: Integer))
                                                                           (coe v6))
                                                                        (coe v10)))
                                                                  (coe
                                                                     d_frame'45'free'45'trace''_494
                                                                     (coe v0)
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                        (coe v1) (coe v12))
                                                                     (coe v13) (coe v10) (coe v15)
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
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
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
                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))))
      MAlonzo.Code.Once.IR.C_In_96 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_Cata_108 v8 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                      -> coe
                           du_cata'45'dispatch'45'ff_438 (coe v0)
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.IRToTrace.du_cata'45'strategy_50
                              (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v14)))
                           (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v14)
                                          (coe v2)))
                                    (coe v2) (coe (0 :: Integer)) (coe v6) (coe v11))))
                           (coe
                              du_trace'45'of_76
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v14)
                                       (coe v2)))
                                 (coe v2) (coe (0 :: Integer)) (coe v6) (coe v11)))
                           (coe
                              d_frame'45'free'45'trace''_494 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v14)
                                    (coe v2)))
                              (coe v2) (coe v11) (coe v4) (coe (0 :: Integer)) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v8 v10
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Out_118 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v8 v9
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Ana_128 v8 v10
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Hylo_136 v7 v9 v10 v12 v13
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_Fuse_144 v7 v9 v10 v12 v13
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.IR.C_const_150 v8 v9
        -> coe
             seq (coe v8)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      MAlonzo.Code.Once.IR.C_SigOp_156 v7 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FrameFreeTrace.frame-free-at-frontier
d_frame'45'free'45'at'45'frontier_702 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_frame'45'free'45'at'45'frontier_702 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace''_396
              (coe v0) (coe v1) (coe v2) (coe v5) (coe (0 :: Integer))
              (coe v3) in
    coe
      (let v7
             = d_frame'45'free'45'trace''_494
                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                 (coe (0 :: Integer)) in
       coe
         (case coe v6 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
              -> case coe v9 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                     -> coe seq (coe v11) (coe v7)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.CCC.Codegen.FrameFreeTrace.ir-to-trace-frame-free
d_ir'45'to'45'trace'45'frame'45'free_730 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ir'45'to'45'trace'45'frame'45'free_730 v0 v1 v2 v3 v4
  = coe
      d_frame'45'free'45'at'45'frontier_702 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe (0 :: Integer))
-- Once.CCC.Codegen.FrameFreeTrace._._.fetch
d_fetch_814 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
d_fetch_814 ~v0 ~v1 = du_fetch_814
du_fetch_814 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218
du_fetch_814 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_214
-- Once.CCC.Codegen.FrameFreeTrace._.fetch-frame-free
d_fetch'45'frame'45'free_972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'frame'45'free_972 v0 ~v1 v2 v3 v4 v5 v6 ~v7
  = du_fetch'45'frame'45'free_972 v0 v2 v3 v4 v5 v6
du_fetch'45'frame'45'free_972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_fetch'45'frame'45'free_972 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch'45'All_1694
      (coe
         MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'trace_732
         (coe v0) (coe v1) (coe v2) (coe v3))
      (coe v5)
      (coe
         d_ir'45'to'45'trace'45'frame'45'free_730 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4))
