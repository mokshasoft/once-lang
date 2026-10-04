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

module MAlonzo.Code.Once.Adequacy.SourceTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.RewriteLinked
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.SourceTrace.isEffUU?
d_isEffUU'63'_8 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEffUU'63'_8 v0
  = let v1
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
              (coe v0) (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_176) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.SourceTrace.mainCall
d_mainCall_22 :: MAlonzo.Code.Once.IR.T_IR_16
d_mainCall_22
  = coe
      MAlonzo.Code.Once.IR.C_Call_136
      (MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.SourceTrace.findMain-here
d_findMain'45'here_26 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_232 ->
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain'45'here_26 ~v0 v1 v2 v3 v4
  = du_findMain'45'here_26 v1 v2 v3 v4
du_findMain'45'here_26 ::
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
du_findMain'45'here_26 v0 v1 v2 v3
  = if coe v0
      then coe v3
      else (case coe v1 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                -> if coe v4
                     then coe
                            seq (coe v5)
                            (case coe v2 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                 -> coe
                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe d_mainCall_22)
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe seq (coe v5) (coe v3)
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.SourceTrace.findMain
d_findMain_44 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain_44 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             du_findMain'45'here_26
             (coe MAlonzo.Code.Once.Compile.d_cfIsPrimitive_248 (coe v1))
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116
                (coe MAlonzo.Code.Once.Compile.d_cfName_242 (coe v1))
                (coe
                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe ("main" :: Data.Text.Text))))
             (coe
                d_isEffUU'63'_8
                (coe MAlonzo.Code.Once.Compile.d_cfType_244 (coe v1)))
             (coe d_findMain_44 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToIR-aux
d_moduleToIR'45'aux_50 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR'45'aux_50 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_44 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToIR
d_moduleToIR_54 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR_54 v0
  = coe
      d_moduleToIR'45'aux_50
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_718
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.SourceTrace.irFunOf
d_irFunOf_58 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_232 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_irFunOf_58 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe MAlonzo.Code.Once.Compile.d_cfName_242 (coe v0))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_dc_66 (coe v0))))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_dc_66 (coe v0)))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_dc_66 (coe v0))))
-- Once.Adequacy.SourceTrace._.dc
d_dc_66 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_232 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dc_66 v0
  = coe
      MAlonzo.Code.Once.Compile.d_directCallIR_14
      (coe MAlonzo.Code.Once.Compile.d_cfType_244 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cfIR_246 (coe v0))
-- Once.Adequacy.SourceTrace.tableOf-go
d_tableOf'45'go_68 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOf'45'go_68 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_tableOf'45'go_68 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_irFunOf_58 (coe v2)) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.tableOf
d_tableOf_78 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOf_78 v0
  = coe
      d_tableOf'45'go_68 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.SourceTrace.tableOfResult
d_tableOfResult_82 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOfResult_82 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_tableOf_78 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleTable
d_moduleTable_86 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_moduleTable_86 v0
  = coe
      d_tableOfResult_82
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_718
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.SourceTrace.programAt
d_programAt_90 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_programAt_90 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v0)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToProgram
d_moduleToProgram_98 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_moduleToProgram_98 v0
  = coe
      d_programAt_90 (coe d_moduleTable_86 (coe v0))
      (coe d_moduleToIR_54 (coe v0))
-- Once.Adequacy.SourceTrace.map-rewrite
d_map'45'rewrite_102 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_map'45'rewrite_102 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe MAlonzo.Code.Once.Type.C_Unit_120))
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe MAlonzo.Code.Once.Type.C_Unit_120))
                   (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToIR-emitted
d_moduleToIR'45'emitted_106 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR'45'emitted_106 v0
  = coe d_map'45'rewrite_102 (coe d_moduleToIR_54 (coe v0))
-- Once.Adequacy.SourceTrace.rewrite-fun
d_rewrite'45'fun_110 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_rewrite'45'fun_110 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
            (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v0))))
-- Once.Adequacy.SourceTrace.rewrite-table
d_rewrite'45'table_114 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_rewrite'45'table_114 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_rewrite'45'fun_110 (coe v1))
             (coe d_rewrite'45'table_114 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.rewrite-program
d_rewrite'45'program_120 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_rewrite'45'program_120 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe
         d_rewrite'45'table_114
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0))))
-- Once.Adequacy.SourceTrace.map-rewrite-program
d_map'45'rewrite'45'program_124 ::
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_map'45'rewrite'45'program_124 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_rewrite'45'program_120 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToProgram-emitted
d_moduleToProgram'45'emitted_128 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_moduleToProgram'45'emitted_128 v0
  = coe
      d_map'45'rewrite'45'program_124 (coe d_moduleToProgram_98 (coe v0))
-- Once.Adequacy.SourceTrace.linkedAt-rewrite
d_linkedAt'45'rewrite_140 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny
d_linkedAt'45'rewrite_140 v0 v1 v2 v3 v4
  = case coe v0 of
      (:) v5 v6
        -> coe
             du_linkedAt'45'rewrite'45'at_158 (coe v6) (coe v1) (coe v2)
             (coe v3)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116
                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v5))
                (coe v1))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v5))
                (coe v2))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v5))
                (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.linkedAt-rewrite-at
d_linkedAt'45'rewrite'45'at_158 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
d_linkedAt'45'rewrite'45'at_158 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_linkedAt'45'rewrite'45'at_158 v1 v2 v3 v4 v5 v6 v7 v8
du_linkedAt'45'rewrite'45'at_158 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
du_linkedAt'45'rewrite'45'at_158 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (case coe v6 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe
                                                      seq (coe v13)
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               else coe
                                                      seq (coe v13)
                                                      (coe
                                                         d_linkedAt'45'rewrite_140 (coe v0) (coe v1)
                                                         (coe v2) (coe v3) (coe v7))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v11)
                                     (coe
                                        d_linkedAt'45'rewrite_140 (coe v0) (coe v1) (coe v2)
                                        (coe v3) (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v9)
                    (coe
                       d_linkedAt'45'rewrite_140 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.linked-retable
d_linked'45'retable_236 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_linked'45'retable_236 ~v0 v1 v2 v3 v4 v5
  = du_linked'45'retable_236 v1 v2 v3 v4 v5
du_linked'45'retable_236 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_linked'45'retable_236 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_linked'45'retable_236 (coe v0) (coe v6) (coe v2) (coe v8)
                       (coe v10))
                    (coe
                       du_linked'45'retable_236 (coe v0) (coe v1) (coe v6) (coe v9)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_linked'45'retable_236 (coe v0) (coe v1) (coe v10) (coe v8)
                              (coe v12))
                           (coe
                              du_linked'45'retable_236 (coe v0) (coe v1) (coe v11) (coe v9)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_linked'45'retable_236 (coe v0) (coe v10) (coe v2) (coe v8)
                              (coe v12))
                           (coe
                              du_linked'45'retable_236 (coe v0) (coe v11) (coe v2) (coe v9)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_84 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
               -> coe
                    du_linked'45'retable_236 (coe v0)
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v9))
                    (coe v10) (coe v8) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_In_94 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           du_linked'45'retable_236 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v12) (coe v2)))
                           (coe v2) (coe v9) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Ana_120 v6 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    du_linked'45'retable_236 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v9) (coe v1))
                    (coe v8) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v6 v7
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_SigOp_130 v5 v6 v7 -> coe v4
      MAlonzo.Code.Once.IR.C_Call_136 v7
        -> coe
             d_linkedAt'45'rewrite_140 (coe v0) (coe v7) (coe v1) (coe v2)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.all-rewrite-linked
d_all'45'rewrite'45'linked_336 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'rewrite'45'linked_336 ~v0 v1 v2 v3
  = du_all'45'rewrite'45'linked_336 v1 v2 v3
du_all'45'rewrite'45'linked_336 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'rewrite'45'linked_336 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       MAlonzo.Code.Once.Adequacy.RewriteLinked.du_rewrite'45'ir'45'linked_324
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                       (coe
                          du_linked'45'retable_236 (coe v0)
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                          (coe v7)))
                    (coe du_all'45'rewrite'45'linked_336 (coe v0) (coe v4) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.rewrite-program-linked
d_rewrite'45'program'45'linked_354 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rewrite'45'program'45'linked_354 ~v0 v1 v2
  = du_rewrite'45'program'45'linked_354 v1 v2
du_rewrite'45'program'45'linked_354 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rewrite'45'program'45'linked_354 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.RewriteLinked.du_rewrite'45'ir'45'linked_324
                (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0))
                (coe
                   du_linked'45'retable_236
                   (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0))
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0))
                   (coe v2)))
             (coe
                du_all'45'rewrite'45'linked_336
                (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0))
                (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.⟦_⟧IR
d_'10214'_'10215'IR_362 ::
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215'IR_362 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Once.Denotation.Behavior.C_mkBehavior_40
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_868 (coe v2)
                (coe d_m_374 (coe v3) (coe v1) (coe v2)))
             (MAlonzo.Code.Once.Denotation.TraceMonad.d_coh_980
                (coe d_pf_376 (coe v3) (coe v1) (coe v2)))
             (MAlonzo.Code.Once.Denotation.TraceMonad.d_bnd_976
                (coe d_pf_376 (coe v3) (coe v1) (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Denotation.Behavior.d_silent_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace._.m
d_m_374 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_m_374 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.Program.d_runIR_392 (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540 (coe v2))
      (coe v0)
-- Once.Adequacy.SourceTrace._.pf
d_pf_376 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_966
d_pf_376 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace'45'pf_1004
      (coe v2) (coe d_m_374 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.SourceTrace.eitherToMaybe
d_eitherToMaybe_378 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_eitherToMaybe_378 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule-aux
d_srcToModule'45'aux_382 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_srcToModule'45'aux_382 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             d_eitherToMaybe_378
             (coe
                MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveImports_1020
                (coe v0) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule
d_srcToModule_390 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_srcToModule_390 v0
  = coe
      d_srcToModule'45'aux_382
      (coe
         MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_202 (coe v0))
      (coe
         d_eitherToMaybe_378
         (coe
            MAlonzo.Code.Once.Parser.d_parseStrict_72
            (coe
               MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204 (coe v0))))
-- Once.Adequacy.SourceTrace.srcToModule-just
d_srcToModule'45'just_400 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_srcToModule'45'just_400 = erased
-- Once.Adequacy.SourceTrace.eitherToMaybe-inv
d_eitherToMaybe'45'inv_424 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eitherToMaybe'45'inv_424 = erased
-- Once.Adequacy.SourceTrace.srcToModule-inv-p
d_srcToModule'45'inv'45'p_442 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_srcToModule'45'inv'45'p_442 ~v0 v1 ~v2 ~v3
  = du_srcToModule'45'inv'45'p_442 v1
du_srcToModule'45'inv'45'p_442 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_srcToModule'45'inv'45'p_442 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule-inv
d_srcToModule'45'inv_462 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_srcToModule'45'inv_462 v0 ~v1 ~v2 = du_srcToModule'45'inv_462 v0
du_srcToModule'45'inv_462 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_srcToModule'45'inv_462 v0
  = coe
      du_srcToModule'45'inv'45'p_442
      (coe
         MAlonzo.Code.Once.Parser.d_parseStrict_72
         (coe MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204 (coe v0)))
-- Once.Adequacy.SourceTrace.sourceTrace-aux
d_sourceTrace'45'aux_470 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_sourceTrace'45'aux_470 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             d_'10214'_'10215'IR_362 (coe d_moduleToProgram_98 (coe v2))
             (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> MAlonzo.Code.Once.Denotation.Behavior.d_silent_42)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.sourceTrace
d_sourceTrace_476 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_sourceTrace_476 v0 v1
  = coe
      d_sourceTrace'45'aux_470 (coe d_srcToModule_390 (coe v0)) (coe v1)
-- Once.Adequacy.SourceTrace.⟦_⟧
d_'10214'_'10215'_482 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215'_482 v0 = coe d_sourceTrace_476 (coe v0)
-- Once.Adequacy.SourceTrace.⟦⟧-via-module
d_'10214''10215''45'via'45'module_492 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''45'via'45'module_492 = erased
