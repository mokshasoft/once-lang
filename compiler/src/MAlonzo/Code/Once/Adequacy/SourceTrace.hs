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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.SourceTrace.isUnit?
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
-- Once.Adequacy.SourceTrace.findMain-here
d_findMain'45'here_12 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
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
                                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_248 v8 v9 v10 v11
                                        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v10)
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe seq (coe v6) (coe v4)
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.SourceTrace.isMain
d_isMain_30 :: MAlonzo.Code.Once.Compile.T_CompiledFun_230 -> Bool
d_isMain_30 v0
  = let v1
          = MAlonzo.Code.Once.Compile.d_cfIsPrimitive_246 (coe v0) in
    coe
      (let v2
             = d_isUnit'63'_8
                 (coe MAlonzo.Code.Once.Compile.d_cfType_242 (coe v0)) in
       coe
         (case coe v1 of
            MAlonzo.Code.Agda.Builtin.Bool.C_false_8
              -> let v3
                       = coe
                           MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                           (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d_parts_8
                              (coe MAlonzo.Code.Once.Compile.d_cfName_240 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d_parts_8
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe ("main" :: Data.Text.Text)))) in
                 coe
                   (case coe v3 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                        -> if coe v4
                             then let v6
                                        = seq
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v4)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased)) in
                                  coe
                                    (case coe v6 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                         -> case coe v7 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v8 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                                       -> case coe v2 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                              -> coe v7
                                                            _ -> coe v1
                                                     _ -> coe v1
                                              _ -> coe v1
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             else (let v6
                                         = seq
                                             (coe v5)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v6 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                 -> case coe v8 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                                        -> case coe v2 of
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                               -> coe v7
                                                             _ -> coe v4
                                                      _ -> coe v4
                                               _ -> coe v4
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Once.Adequacy.SourceTrace.findMain
d_findMain_42 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain_42 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_findMain'45'here_12 (coe v1)
             (coe MAlonzo.Code.Once.Compile.d_cfIsPrimitive_246 (coe v1))
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__16
                (coe MAlonzo.Code.Once.Compile.d_cfName_240 (coe v1))
                (coe
                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe ("main" :: Data.Text.Text))))
             (coe
                d_isUnit'63'_8
                (coe MAlonzo.Code.Once.Compile.d_cfType_242 (coe v1)))
             (coe d_findMain_42 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToIR-aux
d_moduleToIR'45'aux_48 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR'45'aux_48 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_42 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.moduleToIR
d_moduleToIR_52 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR_52 v0
  = coe
      d_moduleToIR'45'aux_48
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_574
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.SourceTrace.⟦_⟧IR
d_'10214'_'10215'IR_56 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_'10214'_'10215'IR_56 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  MAlonzo.Code.Data.List.Base.du_take_530 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                     (coe
                        MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v1)
                        (coe
                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                           (coe MAlonzo.Code.Once.Type.C_Unit_122))
                        (coe
                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                           (coe MAlonzo.Code.Once.Type.C_Unit_122))
                        (coe v2) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                     (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.eitherToMaybe
d_eitherToMaybe_66 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_eitherToMaybe_66 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule-aux
d_srcToModule'45'aux_70 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_srcToModule'45'aux_70 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             d_eitherToMaybe_66
             (coe
                MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveImports_702
                (coe v0) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule
d_srcToModule_78 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_srcToModule_78 v0
  = coe
      d_srcToModule'45'aux_70
      (coe
         MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14 (coe v0))
      (coe
         d_eitherToMaybe_66
         (coe
            MAlonzo.Code.Once.Parser.d_parseStrict_72
            (coe MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16 (coe v0))))
-- Once.Adequacy.SourceTrace.srcToModule-just
d_srcToModule'45'just_88 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_srcToModule'45'just_88 = erased
-- Once.Adequacy.SourceTrace.eitherToMaybe-inv
d_eitherToMaybe'45'inv_112 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eitherToMaybe'45'inv_112 = erased
-- Once.Adequacy.SourceTrace.srcToModule-inv-p
d_srcToModule'45'inv'45'p_130 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_srcToModule'45'inv'45'p_130 ~v0 v1 ~v2 ~v3
  = du_srcToModule'45'inv'45'p_130 v1
du_srcToModule'45'inv'45'p_130 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_srcToModule'45'inv'45'p_130 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule-inv
d_srcToModule'45'inv_150 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_srcToModule'45'inv_150 v0 ~v1 ~v2 = du_srcToModule'45'inv_150 v0
du_srcToModule'45'inv_150 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_srcToModule'45'inv_150 v0
  = coe
      du_srcToModule'45'inv'45'p_130
      (coe
         MAlonzo.Code.Once.Parser.d_parseStrict_72
         (coe MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16 (coe v0)))
-- Once.Adequacy.SourceTrace.sourceTrace-aux
d_sourceTrace'45'aux_158 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_sourceTrace'45'aux_158 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             d_'10214'_'10215'IR_56 (coe d_moduleToIR_52 (coe v2)) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.sourceTrace
d_sourceTrace_166 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_sourceTrace_166 v0 v1
  = coe
      d_sourceTrace'45'aux_158 (coe d_srcToModule_78 (coe v0)) (coe v1)
-- Once.Adequacy.SourceTrace.⟦_⟧
d_'10214'_'10215'_172 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_'10214'_'10215'_172 v0 = coe d_sourceTrace_166 (coe v0)
-- Once.Adequacy.SourceTrace.⟦⟧-via-module
d_'10214''10215''45'via'45'module_182 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''45'via'45'module_182 = erased
