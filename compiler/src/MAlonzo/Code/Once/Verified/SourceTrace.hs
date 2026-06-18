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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ModuleConvert
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.Verified.DenotTrace
import qualified MAlonzo.Code.Once.Verified.MainAlign
import qualified MAlonzo.Code.Once.Verified.SourceSemantics
import qualified MAlonzo.Code.Once.Verified.Trace
import qualified MAlonzo.Code.Once.Verified.TraceMonad
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
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282
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
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282
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
-- Once.Verified.SourceTrace.findMain-name
d_findMain'45'name_42 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_findMain'45'name_42 v0 ~v1 ~v2 = du_findMain'45'name_42 v0
du_findMain'45'name_42 ::
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_findMain'45'name_42 v0
  = case coe v0 of
      (:) v1 v2
        -> let v3
                 = MAlonzo.Code.Once.Compile.d_cfIsPrimitive_202 (coe v1) in
           coe
             (let v4
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v4 ->
                           coe
                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                             (coe MAlonzo.Code.Once.Compile.d_cfName_196 (coe v1)))
                        (coe
                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                           (coe MAlonzo.Code.Once.Compile.d_cfName_196 (coe v1))
                           (coe ("main" :: Data.Text.Text))) in
              coe
                (let v5
                       = d_isUnit'63'_8
                           (coe MAlonzo.Code.Once.Compile.d_cfType_198 (coe v1)) in
                 coe
                   (if coe v3
                      then coe
                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                             (coe du_findMain'45'name_42 (coe v2))
                      else (case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                -> if coe v6
                                     then case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                              -> case coe v5 of
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                     -> coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v8) erased)
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                     -> coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                          (coe du_findMain'45'name_42 (coe v2))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     else coe
                                            seq (coe v7)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                               (coe du_findMain'45'name_42 (coe v2)))
                              _ -> MAlonzo.RTE.mazUnreachableError))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.moduleToIR-aux
d_moduleToIR'45'aux_94 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282
d_moduleToIR'45'aux_94 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_30 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.moduleToIR
d_moduleToIR_98 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282
d_moduleToIR_98 v0
  = coe
      d_moduleToIR'45'aux_94
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_458
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_270)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Verified.SourceTrace.moduleToIR-compiled
d_moduleToIR'45'compiled_106 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_moduleToIR'45'compiled_106 = erased
-- Once.Verified.SourceTrace.sourceToIR
d_sourceToIR_118 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282
d_sourceToIR_118 v0
  = let v1
          = MAlonzo.Code.Once.Grammar.ModuleConvert.d_mapDecls_122
              (coe MAlonzo.Code.Once.Grammar.d_decls_142 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> let v3
                    = coe
                        MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v2) in
              coe (coe d_moduleToIR_98 (coe v3))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> coe d_moduleToIR_98 (coe v2)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceTrace.⟦_⟧IR
d_'10214'_'10215'IR_132 ::
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_'10214'_'10215'IR_132 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  MAlonzo.Code.Data.List.Base.du_take_530 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du_projTrace_62
                     (coe
                        MAlonzo.Code.Once.Verified.DenotTrace.d_eval'7472'_154
                        (coe MAlonzo.Code.Once.Type.C_Unit_122)
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                     (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.main-exists-align
d_main'45'exists'45'align_146 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'exists'45'align_146 v0 ~v1 ~v2
  = du_main'45'exists'45'align_146 v0
du_main'45'exists'45'align_146 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'exists'45'align_146 v0
  = coe
      du_aux_162 (coe v0)
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_458
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_270)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Verified.SourceTrace._.aux
d_aux_162 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_aux_162 v0 ~v1 ~v2 v3 ~v4 ~v5 = du_aux_162 v0 v3
du_aux_162 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_162 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Once.Verified.SourceSemantics.d_lookup'45'main'45'of'45'dfundef_280
             (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
             (coe
                MAlonzo.Code.Once.Verified.MainAlign.du_compileResolvedModule'45'main_1192
                (coe v0) (coe MAlonzo.Code.Once.CCC.IR.C_Heap_270)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe du_findMain'45'name_42 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.compiler-faithful
d_compiler'45'faithful_184
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.SourceTrace.compiler-faithful"
-- Once.Verified.SourceTrace.ProdSim
d_ProdSim_188 ::
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_ProdSim_188 = erased
-- Once.Verified.SourceTrace.compsim⇒prodsim
d_compsim'8658'prodsim_208 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compsim'8658'prodsim_208 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_compsim'8658'prodsim_208 v4
du_compsim'8658'prodsim_208 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compsim'8658'prodsim_208 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  seq (coe v8)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.prod-bridge
d_prod'45'bridge_240
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.SourceTrace.prod-bridge"
-- Once.Verified.SourceTrace.elaborate-faithful
d_elaborate'45'faithful_248 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elaborate'45'faithful_248 = erased
-- Once.Verified.SourceTrace.elaborate-trace-correct
d_elaborate'45'trace'45'correct_264 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elaborate'45'trace'45'correct_264 v0 v1 v2 v3
  = coe d_prod'45'bridge_240 v0 v1 v2 v3
-- Once.Verified.SourceTrace.compiled-main-trace
d_compiled'45'main'45'trace_282 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compiled'45'main'45'trace_282 v0 v1 ~v2 v3 ~v4 v5
  = du_compiled'45'main'45'trace_282 v0 v1 v3 v5
du_compiled'45'main'45'trace_282 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compiled'45'main'45'trace_282 v0 v1 v2 v3
  = let v4 = coe d_compiler'45'faithful_184 v0 v1 erased v2 erased in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> coe
                       seq (coe v8)
                       (coe
                          d_prod'45'bridge_240 v5 v7
                          (MAlonzo.Code.Once.Verified.SourceSemantics.d_extractDefs_230
                             (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                          v3)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceTrace.elaborate-preserves-trace
d_elaborate'45'preserves'45'trace_354 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elaborate'45'preserves'45'trace_354 v0 v1 ~v2 v3
  = du_elaborate'45'preserves'45'trace_354 v0 v1 v3
du_elaborate'45'preserves'45'trace_354 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elaborate'45'preserves'45'trace_354 v0 v1 v2
  = let v3
          = coe
              du_aux_162 (coe v0)
              (let v3 = coe MAlonzo.Code.Once.CCC.IR.C_Heap_270 in
               coe
                 (let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                  coe
                    (let v5
                           = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                               (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v0))
                               (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v5
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> coe
                                        MAlonzo.Code.Once.Compile.d_compileAllFuns_410 (coe v3)
                                        (coe v4) (coe v7)
                                        (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_226 (coe v8))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> let v6
                    = coe d_compiler'45'faithful_184 v0 v1 erased v4 erased in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                     -> case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> coe
                                 seq (coe v10)
                                 (coe
                                    d_prod'45'bridge_240 v7 v9
                                    (MAlonzo.Code.Once.Verified.SourceSemantics.d_extractDefs_230
                                       (coe
                                          MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                                    v2)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceTrace.ElaborateFaithful
d_ElaborateFaithful_400 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> ()
d_ElaborateFaithful_400 = erased
-- Once.Verified.SourceTrace.sourceTrace-aux
d_sourceTrace'45'aux_410 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_sourceTrace'45'aux_410 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe d_'10214'_'10215'IR_132 (coe d_moduleToIR_98 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceTrace.sourceTrace
d_sourceTrace_416 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_sourceTrace_416 v0
  = coe
      d_sourceTrace'45'aux_410
      (coe
         MAlonzo.Code.Once.Grammar.ModuleConvert.d_gmoduleToModule_144
         (coe v0))
-- Once.Verified.SourceTrace.⟦_⟧
d_'10214'_'10215'_420 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_140]
d_'10214'_'10215'_420 v0 = coe d_sourceTrace_416 (coe v0)
-- Once.Verified.SourceTrace.⟦⟧-via-module
d_'10214''10215''45'via'45'module_430 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''45'via'45'module_430 = erased
