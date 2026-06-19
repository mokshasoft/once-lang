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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ModuleConvert
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

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
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_findMain'45'here_12 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else (case coe v2 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                -> if coe v5
                     then coe
                            seq (coe v6)
                            (case coe v3 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                 -> case coe v0 of
                                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_204 v8 v9 v10 v11
                                        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v10)
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe seq (coe v6) (coe v4)
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceTrace.findMain
d_findMain_30 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_findMain_30 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_findMain'45'here_12 (coe v1)
             (coe MAlonzo.Code.Once.Compile.d_cfIsPrimitive_202 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Compile.d_cfName_196 (coe v1))
                (coe ("main" :: Data.Text.Text)))
             (coe
                d_isUnit'63'_8
                (coe MAlonzo.Code.Once.Compile.d_cfType_198 (coe v1)))
             (coe d_findMain_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.moduleToIR-aux
d_moduleToIR'45'aux_36 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_moduleToIR'45'aux_36 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_30 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.moduleToIR
d_moduleToIR_40 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274
d_moduleToIR_40 v0
  = coe
      d_moduleToIR'45'aux_36
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_458
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Verified.SourceTrace.⟦_⟧IR
d_'10214'_'10215'IR_44 ::
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_'10214'_'10215'IR_44 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  MAlonzo.Code.Data.List.Base.du_take_530 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                     (coe
                        MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_154
                        (coe MAlonzo.Code.Once.Type.C_Unit_122)
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                     (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.sourceTrace-aux
d_sourceTrace'45'aux_52 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_sourceTrace'45'aux_52 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe d_'10214'_'10215'IR_44 (coe d_moduleToIR_40 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.sourceTrace
d_sourceTrace_58 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_sourceTrace_58 v0
  = coe
      d_sourceTrace'45'aux_52
      (coe
         MAlonzo.Code.Once.Grammar.ModuleConvert.d_gmoduleToModule_144
         (coe v0))
-- Once.Verified.SourceTrace.⟦_⟧
d_'10214'_'10215'_62 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_'10214'_'10215'_62 v0 = coe d_sourceTrace_58 (coe v0)
-- Once.Verified.SourceTrace.⟦⟧-via-module
d_'10214''10215''45'via'45'module_72 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''45'via'45'module_72 = erased
