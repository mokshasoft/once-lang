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

module MAlonzo.Code.Once.Denotation.Program where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.Program.IRFun
d_IRFun_6 = ()
data T_IRFun_6
  = C_irFun_24 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
               MAlonzo.Code.Once.IRTy.T_IRTy_6 MAlonzo.Code.Once.IRTy.T_IRTy_6
               MAlonzo.Code.Once.IR.T_IR_16
-- Once.Denotation.Program.IRFun.fname
d_fname_16 ::
  T_IRFun_6 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_fname_16 v0
  = case coe v0 of
      C_irFun_24 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.IRFun.fdom
d_fdom_18 :: T_IRFun_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_fdom_18 v0
  = case coe v0 of
      C_irFun_24 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.IRFun.fcod
d_fcod_20 :: T_IRFun_6 -> MAlonzo.Code.Once.IRTy.T_IRTy_6
d_fcod_20 v0
  = case coe v0 of
      C_irFun_24 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.IRFun.fbody
d_fbody_22 :: T_IRFun_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_fbody_22 v0
  = case coe v0 of
      C_irFun_24 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.tableEnv
d_tableEnv_26 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  [T_IRFun_6] -> MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6
d_tableEnv_26 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.C_callEnv_24
      (coe d_tableCalls_32 (coe v0) (coe v1) (coe v2)) (coe v1)
-- Once.Denotation.Program.tableCalls
d_tableCalls_32 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  [T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_tableCalls_32 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_embed_136
             (coe MAlonzo.Code.Once.Internal.Trace.du_unlinkedT_228)
      (:) v7 v8
        -> coe
             d_tableEnv'45'at_42 (coe v0) (coe v1) (coe v7) (coe v8) (coe v3)
             (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                (coe d_fname_16 (coe v7)) (coe v3))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196 (coe d_fdom_18 (coe v7))
                (coe v4))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196 (coe d_fcod_20 (coe v7))
                (coe v5))
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.tableEnv-at
d_tableEnv'45'at_42 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  T_IRFun_6 ->
  [T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_tableEnv'45'at_42 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then coe
                    seq (coe v12)
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                         -> if coe v13
                              then coe
                                     seq (coe v14)
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                          -> if coe v15
                                               then coe
                                                      seq (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                                                         (coe v0)
                                                         (coe
                                                            d_tableEnv_26 (coe v0) (coe v1)
                                                            (coe v3))
                                                         (coe d_fdom_18 (coe v2))
                                                         (coe d_fcod_20 (coe v2))
                                                         (coe d_fbody_22 (coe v2)) (coe v10))
                                               else coe
                                                      seq (coe v16)
                                                      (coe
                                                         d_tableCalls_32 (coe v0) (coe v1) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v10))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v14)
                                     (coe
                                        d_tableCalls_32 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                                        (coe v6) (coe v10))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v12)
                    (coe
                       d_tableCalls_32 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.LinkedAt
d_LinkedAt_148 ::
  [T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_LinkedAt_148 = erased
-- Once.Denotation.Program.LinkedAt-at
d_LinkedAt'45'at_158 ::
  T_IRFun_6 ->
  [T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> ()
d_LinkedAt'45'at_158 = erased
-- Once.Denotation.Program.Declared-at
d_Declared'45'at_220 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> ()
d_Declared'45'at_220 = erased
-- Once.Denotation.Program.Declared
d_Declared_258 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 -> ()
d_Declared_258 = erased
-- Once.Denotation.Program.Linked
d_Linked_268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Linked_268 = erased
-- Once.Denotation.Program.IRProgram
d_IRProgram_386 = ()
data T_IRProgram_386
  = C_irProgram_396 [T_IRFun_6] MAlonzo.Code.Once.IR.T_IR_16
-- Once.Denotation.Program.IRProgram.table
d_table_392 :: T_IRProgram_386 -> [T_IRFun_6]
d_table_392 v0
  = case coe v0 of
      C_irProgram_396 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.IRProgram.main
d_main_394 :: T_IRProgram_386 -> MAlonzo.Code.Once.IR.T_IR_16
d_main_394 v0
  = case coe v0 of
      C_irProgram_396 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Program.runIR
d_runIR_398 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  T_IRProgram_386 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_runIR_398 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe d_tableEnv_26 (coe v0) (coe v1) (coe d_table_392 (coe v2)))
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe d_main_394 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Denotation.Program.TeleLinked
d_TeleLinked_406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_IRFun_6] -> ()
d_TeleLinked_406 = erased
-- Once.Denotation.Program.NamesDistinct
d_NamesDistinct_416 :: [T_IRFun_6] -> ()
d_NamesDistinct_416 = erased
-- Once.Denotation.Program.LinkedProgram
d_LinkedProgram_422 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_IRProgram_386 -> ()
d_LinkedProgram_422 = erased
