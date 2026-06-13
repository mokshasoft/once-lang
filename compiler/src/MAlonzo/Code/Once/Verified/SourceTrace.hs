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

module MAlonzo.Code.Once.Verified.SourceTrace where

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
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ModuleConvert
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Verified.SourceSemantics
import qualified MAlonzo.Code.Once.Verified.Trace
import qualified MAlonzo.Code.Once.Verified.TraceDenote
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Verified.SourceTrace.isUnit?
d_isUnit'63'_8 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isUnit'63'_8 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
         _ -> coe v1)
-- Once.Verified.SourceTrace.findMain-here
d_findMain'45'here_12 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_186 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_findMain'45'here_12 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> case coe v0 of
                              MAlonzo.Code.Once.Compile.C_mkCompiledFun_204 v7 v8 v9 v10
                                -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v9)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.findMain
d_findMain_26 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_findMain_26 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_findMain'45'here_12 (coe v1)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Compile.d_cfName_196 (coe v1))
                (coe ("main" :: Data.Text.Text)))
             (coe
                d_isUnit'63'_8
                (coe MAlonzo.Code.Once.Compile.d_cfType_198 (coe v1)))
             (coe d_findMain_26 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.findMain-name
d_findMain'45'name_38 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_findMain'45'name_38 v0 ~v1 ~v2 = du_findMain'45'name_38 v0
du_findMain'45'name_38 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_findMain'45'name_38 v0
  = case coe v0 of
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe MAlonzo.Code.Once.Compile.d_cfName_196 (coe v1)))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                        (coe MAlonzo.Code.Once.Compile.d_cfName_196 (coe v1))
                        (coe ("main" :: Data.Text.Text))) in
           coe
             (let v4
                    = d_isUnit'63'_8
                        (coe MAlonzo.Code.Once.Compile.d_cfType_198 (coe v1)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then case coe v6 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                   -> case coe v4 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                          -> coe
                                               MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                               v7
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe
                                               MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                               (coe du_findMain'45'name_38 (coe v2))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else coe
                                 seq (coe v6)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                    (coe du_findMain'45'name_38 (coe v2)))
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.moduleToIR-aux
d_moduleToIR'45'aux_80 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_moduleToIR'45'aux_80 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_26 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.moduleToIR
d_moduleToIR_84 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_moduleToIR_84 v0
  = coe
      d_moduleToIR'45'aux_80
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_414
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Verified.SourceTrace.moduleToIR-compiled
d_moduleToIR'45'compiled_92 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_moduleToIR'45'compiled_92 = erased
-- Once.Verified.SourceTrace.sourceToIR
d_sourceToIR_104 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_sourceToIR_104 v0
  = let v1
          = MAlonzo.Code.Once.Grammar.ModuleConvert.d_mapDecls_122
              (coe MAlonzo.Code.Once.Grammar.d_decls_142 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> let v3
                    = coe
                        MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v2) in
              coe (coe d_moduleToIR_84 (coe v3))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> coe d_moduleToIR_84 (coe v2)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceTrace.⟦_⟧IR
d_'10214'_'10215'IR_118 ::
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_'10214'_'10215'IR_118 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Once.Verified.TraceDenote.d_obs_56
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v2) (coe v1)
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.main-exists-align
d_main'45'exists'45'align_132
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.SourceTrace.main-exists-align"
-- Once.Verified.SourceTrace.compiled-main-trace
d_compiled'45'main'45'trace_142
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.SourceTrace.compiled-main-trace"
-- Once.Verified.SourceTrace.elaborate-preserves-trace
d_elaborate'45'preserves'45'trace_150 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elaborate'45'preserves'45'trace_150 = erased
-- Once.Verified.SourceTrace.sourceTrace-aux
d_sourceTrace'45'aux_176 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_sourceTrace'45'aux_176 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Once.Verified.SourceSemantics.d_runTrace_756 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.sourceTrace
d_sourceTrace_182 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_sourceTrace_182 v0
  = coe
      d_sourceTrace'45'aux_176
      (coe
         MAlonzo.Code.Once.Grammar.ModuleConvert.d_gmoduleToModule_144
         (coe v0))
-- Once.Verified.SourceTrace.⟦_⟧
d_'10214'_'10215'_186 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_'10214'_'10215'_186 v0 = coe d_sourceTrace_182 (coe v0)
-- Once.Verified.SourceTrace.⟦⟧-via-module
d_'10214''10215''45'via'45'module_196 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''45'via'45'module_196 = erased
