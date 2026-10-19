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

module MAlonzo.Code.Once.Adequacy.TableCall where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.EvalRel
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.TableCall.tableEnv-skip
d_tableEnv'45'skip_22 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableEnv'45'skip_22 = erased
-- Once.Adequacy.TableCall.tableEnv-hit
d_tableEnv'45'hit_84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableEnv'45'hit_84 = erased
-- Once.Adequacy.TableCall.abiT
d_abiT_158 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_abiT_158 ~v0 ~v1 v2 v3 = du_abiT_158 v2 v3
du_abiT_158 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_abiT_158 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                       (coe
                          (\ v7 ->
                             coe
                               MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                               (coe v1) (coe (\ v8 -> coe v8 v7)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TableCall.uncurry-app
d_uncurry'45'app_248 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_uncurry'45'app_248 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_uncurry'45'app_248 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_uncurry'45'app_248 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_uncurry'45'app_248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'assoc'737'_696
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
            (coe v3) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
            (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe v5)
         (coe
            (\ v10 ->
               coe
                 MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__78
                 (coe
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                    (coe v3) (coe v1) (coe v1) (coe MAlonzo.Code.Once.IR.C_id_20)
                    (coe v7))
                 (coe
                    (\ v11 ->
                       coe
                         MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_70
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                            (coe v11))))))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
            (coe v3)
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
               (coe v1))
            (coe v2) (coe MAlonzo.Code.Once.IR.C_apply_90))
         (coe (\ v10 -> coe v10 v8)) (coe v6)
         (coe
            (\ v10 v11 v12 ->
               coe
                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                 (coe v12 v7 v8 v9))))
-- Once.Adequacy.TableCall.self
d_self_272 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_self_272 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Denotation.EvalRel.d_eval'45'rel_392 v0
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
            (coe v1) (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe v1) (coe v4))))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableCalls_32 (coe v0)
            (coe v1) (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe
               MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
               (coe v1) (coe v4))))
      (MAlonzo.Code.Once.Denotation.EvalRel.d_table'45'self_656
         (coe v0) (coe v1) (coe v4))
      v2 v3 v5 v6 v7 v8
-- Once.Adequacy.TableCall.abi
d_abi_288 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_abi_288 v0 v1 v2 ~v3 v4 v5 = du_abi_288 v0 v1 v2 v4 v5
du_abi_288 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_abi_288 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v5 v6
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v5 v6
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v5 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                           (coe
                              (\ v10 v11 v12 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                   (coe
                                      du_uncurry'45'app_248 (coe v0)
                                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                                         (coe v1) (coe v3))
                                      (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                         (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26
                                            (coe v0) (coe v1) (coe v3))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                                         (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                      (coe
                                         d_self_272 (coe v0) (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                                         (coe v3) (coe v4)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v12))))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                           (coe
                              (\ v10 v11 v12 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                   (coe
                                      du_uncurry'45'app_248 (coe v0)
                                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5))
                                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                                         (coe v1) (coe v3))
                                      (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                         (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26
                                            (coe v0) (coe v1) (coe v3))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                                         (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                      (coe
                                         d_self_272 (coe v0) (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                                         (coe v3) (coe v4)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                      (coe v10) (coe v11) (coe v12))))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                           (coe
                              (\ v10 v11 v12 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                   (coe
                                      du_uncurry'45'app_248 (coe v0)
                                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5))
                                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                                         (coe v1) (coe v3))
                                      (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                         (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26
                                            (coe v0) (coe v1) (coe v3))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                                         (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                      (coe
                                         d_self_272 (coe v0) (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
                                         (coe v3) (coe v4)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                      (coe v10) (coe v11) (coe v12))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v5
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v5 v6
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v5 v6
        -> coe
             MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
             (coe
                d_self_272 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v3)
                (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
