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

module MAlonzo.Code.Once.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Escape
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Desugar
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Target.RiscV64
import qualified MAlonzo.Code.Once.Target.X86Z45Z32
import qualified MAlonzo.Code.Once.Target.X86Z45Z64
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Compile.validateMain
d_validateMain_4 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_validateMain_4 v0
  = let v1
          = coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
              (coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                 ("main must have type IO Unit (= Eff Unit Unit), but got: "
                  ::
                  Data.Text.Text)
                 (MAlonzo.Code.Once.Type.d_showType_202 (coe v0))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Unit_122
                  -> case coe v3 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> case coe v6 of
                                     MAlonzo.Code.Once.Type.C_eff_36
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Type.C_Unit_122
                                              -> coe
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> coe v1
                                     _ -> coe v1
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.Compile.wrapMainAsEntry
d_wrapMainAsEntry_8 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_wrapMainAsEntry_8 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
            (coe MAlonzo.Code.Once.Type.C_Unit_122)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_eff_36))
            (coe MAlonzo.Code.Once.Type.C_Unit_122))
         (coe MAlonzo.Code.Once.Type.C_Unit_122))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_352)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v0
         (coe MAlonzo.Code.Once.CCC.IR.C_terminal_330)
         (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260))
-- Once.Compile.maybeWrapMain
d_maybeWrapMain_18 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_maybeWrapMain_18 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2) in
    coe
      (case coe v0 of
         l | (==) l ("main" :: Data.Text.Text) ->
             case coe v1 of
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v4 v5 v6
                 -> case coe v4 of
                      MAlonzo.Code.Once.Type.C_Unit_122
                        -> case coe v5 of
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                               -> case coe v7 of
                                    MAlonzo.Code.Once.Type.C_Many_10
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.Type.C_eff_36
                                             -> case coe v6 of
                                                  MAlonzo.Code.Once.Type.C_Unit_122
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v6) (coe d_wrapMainAsEntry_8 (coe v2))
                                                  _ -> coe v3
                                           _ -> coe v3
                                    _ -> coe v3
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> coe v3
               _ -> coe v3
         _ -> coe v3)
-- Once.Compile.FunCtx
d_FunCtx_26 :: ()
d_FunCtx_26 = erased
-- Once.Compile.emptyFunCtx
d_emptyFunCtx_28 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyFunCtx_28 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Compile.extendFunCtx
d_extendFunCtx_30 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendFunCtx_30 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.Compile.compileFunBody
d_compileFunBody_42 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_42 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1062
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_184
                    (coe v2) (coe v3) (coe v4) (coe v5))
                 (coe v6) (coe v5)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_276 v8 v9 v10 v11
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Optimize.d_optimize_4088
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_'10214'_'10215''7580'_44
                         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8))
                      v5
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_118
                         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v5) (coe v0)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_12538
                            (coe (0 :: Integer))
                            (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v5) (coe v3)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))
                               (coe v2))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))
                               (coe v2))
                            (coe (0 :: Integer)) (coe v9))))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_118
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v5) (coe v0)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_12538
                         (coe (0 :: Integer))
                         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v5) (coe v3)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))
                            (coe v2))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))
                            (coe v2))
                         (coe (0 :: Integer)) (coe v9))))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_278 v8
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Type error in " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v4
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (": " :: Data.Text.Text)
                         (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_76 (coe v8)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.compileFun
d_compileFun_104 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_104 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v7 ->
                    coe
                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                      (coe v4))
                 (coe
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                    (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                    (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                       ("main" :: Data.Text.Text)))) in
    coe
      (if coe v7
         then let v8 = d_validateMain_4 (coe v5) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                     -> coe
                          d_compileFunBody_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v6)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                d_compileFunBody_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6))
-- Once.Compile.CompiledFun
d_CompiledFun_186 = ()
data T_CompiledFun_186
  = C_mkCompiledFun_204 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_Type_112 MAlonzo.Code.Once.CCC.IR.T_IR_274
                        Bool
-- Once.Compile.CompiledFun.cfName
d_cfName_196 ::
  T_CompiledFun_186 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_cfName_196 v0
  = case coe v0 of
      C_mkCompiledFun_204 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_198 ::
  T_CompiledFun_186 -> MAlonzo.Code.Once.Type.T_Type_112
d_cfType_198 v0
  = case coe v0 of
      C_mkCompiledFun_204 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_200 ::
  T_CompiledFun_186 -> MAlonzo.Code.Once.CCC.IR.T_IR_274
d_cfIR_200 v0
  = case coe v0 of
      C_mkCompiledFun_204 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIsPrimitive
d_cfIsPrimitive_202 :: T_CompiledFun_186 -> Bool
d_cfIsPrimitive_202 v0
  = case coe v0 of
      C_mkCompiledFun_204 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_206 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_206 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_28
      (:) v1 v2
        -> coe
             d_extendFunCtx_30 (coe d_buildFunCtx_206 (coe v2))
             (coe MAlonzo.Code.Once.Parser.d_funName_96 (coe v1))
             (coe MAlonzo.Code.Once.Parser.d_funType_98 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_212 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_108] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_212 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyPolyCtx_12
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.d_pfunName_118 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Parser.d_pfunType_120 (coe v1))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_124 (coe v1))))
             (coe d_buildPolyCtx_212 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns
d_compileAllFuns_218 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns_218 v0 v1 v2 v3
  = coe
      du_go_232 (coe v0) (coe v1) (coe v3) (coe v2)
      (coe d_emptyFunCtx_28)
-- Once.Compile._.go
d_go_232 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_232 v0 v1 ~v2 v3 v4 v5 = du_go_232 v0 v1 v3 v4 v5
du_go_232 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_232 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v5 v6
        -> let v7 = MAlonzo.Code.Once.Parser.d_funName_96 (coe v5) in
           coe
             (let v8
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                           erased
                           (\ v8 ->
                              coe
                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                (coe MAlonzo.Code.Once.Parser.d_funName_96 (coe v5)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                              (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                 (MAlonzo.Code.Once.Parser.d_funName_96 (coe v5)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                 ("main" :: Data.Text.Text)))) in
              coe
                (let v9 = MAlonzo.Code.Once.Parser.d_funType_98 (coe v5) in
                 coe
                   (let v10 = MAlonzo.Code.Once.Parser.d_funBody_102 (coe v5) in
                    coe
                      (if coe v8
                         then let v11 = d_validateMain_4 (coe v9) in
                              coe
                                (case coe v11 of
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                     -> case coe v11 of
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13 -> coe v11
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                            -> let v14
                                                     = coe
                                                         du_go_232 (coe v0) (coe v1) (coe v2)
                                                         (coe v6)
                                                         (coe
                                                            d_extendFunCtx_30 (coe v4)
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funName_96
                                                               (coe v5))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funType_98
                                                               (coe v5))) in
                                               coe
                                                 (case coe v14 of
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                                      -> coe v14
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                                      -> coe
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 C_mkCompiledFun_204
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_96
                                                                    (coe v5))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                    (coe
                                                                       d_maybeWrapMain_18
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funName_96
                                                                          (coe v5))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funType_98
                                                                          (coe v5))
                                                                       (coe v13)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                    (coe
                                                                       d_maybeWrapMain_18
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funName_96
                                                                          (coe v5))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funType_98
                                                                          (coe v5))
                                                                       (coe v13)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funIsPrimitive_104
                                                                    (coe v5)))
                                                              (coe v15))
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                     -> let v13
                                              = d_compileFunBody_42
                                                  (coe v0) (coe v1) (coe v4) (coe v2) (coe v7)
                                                  (coe v9) (coe v10) in
                                        coe
                                          (case coe v13 of
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                               -> coe v13
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                               -> let v15
                                                        = coe
                                                            du_go_232 (coe v0) (coe v1) (coe v2)
                                                            (coe v6)
                                                            (coe
                                                               d_extendFunCtx_30 (coe v4)
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_funName_96
                                                                  (coe v5))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_funType_98
                                                                  (coe v5))) in
                                                  coe
                                                    (case coe v15 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                                                         -> coe v15
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                                                         -> coe
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    C_mkCompiledFun_204
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.d_funName_96
                                                                       (coe v5))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                       (coe
                                                                          d_maybeWrapMain_18
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funName_96
                                                                             (coe v5))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funType_98
                                                                             (coe v5))
                                                                          (coe v14)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                       (coe
                                                                          d_maybeWrapMain_18
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funName_96
                                                                             (coe v5))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funType_98
                                                                             (coe v5))
                                                                          (coe v14)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.d_funIsPrimitive_104
                                                                       (coe v5)))
                                                                 (coe v16))
                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                   _ -> MAlonzo.RTE.mazUnreachableError)
                         else (let v11
                                     = d_compileFunBody_42
                                         (coe v0) (coe v1) (coe v4) (coe v2) (coe v7) (coe v9)
                                         (coe v10) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12 -> coe v11
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                      -> let v13
                                               = coe
                                                   du_go_232 (coe v0) (coe v1) (coe v2) (coe v6)
                                                   (coe
                                                      d_extendFunCtx_30 (coe v4)
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funName_96
                                                         (coe v5))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funType_98
                                                         (coe v5))) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                                -> coe v13
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                                -> coe
                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           C_mkCompiledFun_204
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_funName_96
                                                              (coe v5))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                              (coe
                                                                 d_maybeWrapMain_18
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_96
                                                                    (coe v5))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funType_98
                                                                    (coe v5))
                                                                 (coe v12)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_maybeWrapMain_18
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_96
                                                                    (coe v5))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funType_98
                                                                    (coe v5))
                                                                 (coe v12)))
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_funIsPrimitive_104
                                                              (coe v5)))
                                                        (coe v14))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileModule
d_compileModule_290 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_290 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v3
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v2) in
                  coe
                    (let v4
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v2)) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> let v8
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v7) in
                                      coe
                                        (let v9
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v3) in
                                         coe
                                           (case coe v8 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                -> case coe v10 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                              -> let v15
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                           (coe v13) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                        -> case coe v17 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v11)
                                                                                       (coe v16))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v18)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v19)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v14))
                                                                                             (coe
                                                                                                v9))))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v7) (coe v9))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v5 v6 -> addInt (coe (1 :: Integer)) (coe v6)))
                                          (coe (0 :: Integer)) (coe v3))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe
      (let v4
             = MAlonzo.Code.Once.Parser.d_extractFunctions_156
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v3))
                 (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
              -> case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> coe
                          d_compileAllFuns_218 (coe v0) (coe v1) (coe v6)
                          (coe d_buildPolyCtx_212 (coe v7))
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_326 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_326
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_32
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_328 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_328 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_extractFunctions_156
              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v2))
              (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       d_compileAllFuns_218 (coe v0) (coe v1) (coe v5)
                       (coe d_buildPolyCtx_212 (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.pipeline
d_pipeline_350 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline_350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Escape.d_escape_126 v0 v1
      (coe
         MAlonzo.Code.Once.Optimize.d_optimize_4088 v0 v1
         (MAlonzo.Code.Once.Surface.Desugar.d_desugar_18
            (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Compile.pipeline-default
d_pipeline'45'default_360 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline'45'default_360 v0 v1
  = coe
      d_pipeline_350 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
-- Once.Compile.pipeline-no-escape
d_pipeline'45'no'45'escape_366 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline'45'no'45'escape_366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Optimize.d_optimize_4088 v0 v1
      (MAlonzo.Code.Once.Surface.Desugar.d_desugar_18
         (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Compile.pipeline-no-opt
d_pipeline'45'no'45'opt_376 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline'45'no'45'opt_376 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Desugar.d_desugar_18 (coe v0) (coe v1)
-- Once.Compile.Arch
d_Arch_378 = ()
data T_Arch_378 = C_x86'45'64_380 | C_x86'45'32_382 | C_riscv64_384
-- Once.Compile.archTarget
d_archTarget_386 ::
  T_Arch_378 -> MAlonzo.Code.Once.Target.T_Target_4
d_archTarget_386 v0
  = case coe v0 of
      C_x86'45'64_380
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.d_x86'45'64_84
      C_x86'45'32_382
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.d_x86'45'32_36
      C_riscv64_384 -> coe MAlonzo.Code.Once.Target.RiscV64.d_riscv64_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunWithTarget
d_compileFunWithTarget_388 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunWithTarget_388 v0 v1 v2
  = let v3 = d_cfIsPrimitive_202 (coe v2) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe ("" :: Data.Text.Text))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         else coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Target.d_irToAsm_30 v0 v1
                         (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_198 (coe v2))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                               (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe d_cfType_198 (coe v2))
                               (coe d_cfIR_200 (coe v2))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Target.d_irToBodies_36 v0 v1
                         (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_198 (coe v2))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                               (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe d_cfType_198 (coe v2))
                               (coe d_cfIR_200 (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe
                         MAlonzo.Code.Once.Target.d_functionPrologue_40 v0
                         (d_cfName_196 (coe v2)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Target.d_irToAsm_30 v0 v1
                               (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_198 (coe v2))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                     (coe d_cfType_198 (coe v2)) (coe d_cfIR_200 (coe v2))))))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Once.Target.d_functionEpilogue_42 (coe v0))
                            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Once.Target.d_irToBodies_36 v0 v1
                                  (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_198 (coe v2))
                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                                        (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                        (coe d_cfType_198 (coe v2)) (coe d_cfIR_200 (coe v2)))))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                         (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe d_cfType_198 (coe v2))
                         (coe d_cfIR_200 (coe v2))))))
-- Once.Compile.compileAllWithTarget
d_compileAllWithTarget_424 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_186] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAllWithTarget_424 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_434 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe ("" :: Data.Text.Text))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
               (coe v1))))
      (coe
         MAlonzo.Code.Once.Target.d_emitArithBlocks_44 v0
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_434 (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe ("" :: Data.Text.Text))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe v1)))))
-- Once.Compile._.step
d_step_434 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_186] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_434 v0 ~v1 v2 v3 = du_step_434 v0 v2 v3
du_step_434 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_434 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_compileFunWithTarget_388 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     d_compileFunWithTarget_388 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                     (coe v2)))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     d_compileFunWithTarget_388 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                     (coe v2))))))
-- Once.Compile.Stage
d_Stage_456 = ()
data T_Stage_456 = C_Parse_458 | C_Check_460 | C_Build_462
-- Once.Compile.CompileResult
d_CompileResult_464 = ()
data T_CompileResult_464
  = C_Parsed_466 [MAlonzo.Code.Once.Parser.T_FunInfo_84]
                 [MAlonzo.Code.Once.Parser.T_PolyFunInfo_108] |
    C_Checked_468 [T_CompiledFun_186] |
    C_Built_470 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_472 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.showFunInfo
d_showFunInfo_474 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_474 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_funName_96 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showType_202
            (coe MAlonzo.Code.Once.Parser.d_funType_98 (coe v0))))
-- Once.Compile.showPolyFunInfo
d_showPolyFunInfo_478 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_478 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_118 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_464
            (coe MAlonzo.Code.Once.Parser.d_pfunType_120 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_482 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_482 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_474 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_482 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_474 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_490 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_108] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_490 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_478 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_490 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_478 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_498 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  T_Stage_456 ->
  Bool ->
  T_Arch_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_464
d_compile_498 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (let v5
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v4) in
                  coe
                    (let v6
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_398
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                   -> let v10
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v9) in
                                      coe
                                        (let v11
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v5) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                -> case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                       -> case coe v14 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                              -> let v17
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                           (coe v15) in
                                                                 coe
                                                                   (case coe v17 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                        -> case coe v19 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v13)
                                                                                       (coe v18))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v20)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v21)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v16))
                                                                                             (coe
                                                                                                v11))))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v9) (coe v11))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v7 v8 -> addInt (coe (1 :: Integer)) (coe v8)))
                                          (coe (0 :: Integer)) (coe v5))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe
      (let v6
             = MAlonzo.Code.Once.Parser.d_allTrailing_18
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (let v6
                              = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v4) in
                        coe
                          (let v7
                                 = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_398
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           v4)) in
                           coe
                             (case coe v7 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                  -> case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                         -> let v11
                                                  = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                      (coe v10) in
                                            coe
                                              (let v12
                                                     = coe
                                                         MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                         (coe v6) in
                                               coe
                                                 (case coe v11 of
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                      -> case coe v13 of
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                             -> case coe v15 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                    -> let v18
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                                 (coe v16) in
                                                                       coe
                                                                         (case coe v18 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                              -> case coe v20 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                     -> coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                v14)
                                                                                             (coe
                                                                                                v19))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v21)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                                (coe
                                                                                                   v22)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                      (coe
                                                                                                         v17))
                                                                                                   (coe
                                                                                                      v12))))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      -> coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v10) (coe v12))
                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                (coe
                                                   (\ v8 v9 ->
                                                      addInt (coe (1 :: Integer)) (coe v9)))
                                                (coe (0 :: Integer)) (coe v6))))
                                _ -> MAlonzo.RTE.mazUnreachableError))))) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (let v7
                              = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v4) in
                        coe
                          (let v8
                                 = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630
                                        (coe v4)) in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                  -> case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                         -> let v12
                                                  = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                      (coe v11) in
                                            coe
                                              (let v13
                                                     = coe
                                                         MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                         (coe v7) in
                                               coe
                                                 (case coe v12 of
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                      -> case coe v14 of
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                             -> case coe v16 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                    -> let v19
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                                 (coe v17) in
                                                                       coe
                                                                         (case coe v19 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                              -> case coe v21 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                     -> coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                v15)
                                                                                             (coe
                                                                                                v20))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v22)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                                (coe
                                                                                                   v23)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                      (coe
                                                                                                         v18))
                                                                                                   (coe
                                                                                                      v13))))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                      -> coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v11) (coe v13))
                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                (coe
                                                   (\ v9 v10 ->
                                                      addInt (coe (1 :: Integer)) (coe v10)))
                                                (coe (0 :: Integer)) (coe v7))))
                                _ -> MAlonzo.RTE.mazUnreachableError)))) in
          coe
            (if coe v6
               then let v8
                          = MAlonzo.Code.Once.Parser.d_extractFunctions_156
                              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v7))
                              (coe v7) in
                    coe
                      (case coe v8 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                           -> coe C_Error_472 (coe v9)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                           -> case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                  -> case coe v1 of
                                       C_Parse_458 -> coe C_Parsed_466 (coe v10) (coe v11)
                                       C_Check_460
                                         -> let v12
                                                  = d_compileAllFuns_218
                                                      (coe v0) (coe v2) (coe v10)
                                                      (coe d_buildPolyCtx_212 (coe v11)) in
                                            coe
                                              (case coe v12 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                                   -> coe C_Error_472 (coe v13)
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                                   -> coe C_Checked_468 (coe v13)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       C_Build_462
                                         -> let v12
                                                  = d_compileAllFuns_218
                                                      (coe v0) (coe v2) (coe v10)
                                                      (coe d_buildPolyCtx_212 (coe v11)) in
                                            coe
                                              (case coe v12 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                                   -> coe C_Error_472 (coe v13)
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                                   -> coe
                                                        C_Built_470
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           (MAlonzo.Code.Once.Target.d_asmHeader_38
                                                              (coe d_archTarget_386 (coe v3)))
                                                           (d_compileAllWithTarget_424
                                                              (coe d_archTarget_386 (coe v3))
                                                              (coe v13)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError
                         _ -> MAlonzo.RTE.mazUnreachableError)
               else (let v8
                           = coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("Parse error: unexpected tokens remaining after last parsed decl (starting at: "
                                ::
                                Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (MAlonzo.Code.Once.Parser.d_showTokenPrefix_24 (coe v5))
                                  (")" :: Data.Text.Text)) in
                     coe (coe C_Error_472 (coe v8))))))
-- Once.Compile.compileFromModule
d_compileFromModule_566 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  T_Stage_456 ->
  Bool ->
  T_Arch_378 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  T_CompileResult_464
d_compileFromModule_566 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Parser.d_extractFunctions_156
              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v4))
              (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> coe C_Error_472 (coe v6)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v1 of
                       C_Parse_458 -> coe C_Parsed_466 (coe v7) (coe v8)
                       C_Check_460
                         -> let v9
                                  = d_compileAllFuns_218
                                      (coe v0) (coe v2) (coe v7)
                                      (coe d_buildPolyCtx_212 (coe v8)) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                   -> coe C_Error_472 (coe v10)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                   -> coe C_Checked_468 (coe v10)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_Build_462
                         -> let v9
                                  = d_compileAllFuns_218
                                      (coe v0) (coe v2) (coe v7)
                                      (coe d_buildPolyCtx_212 (coe v8)) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                   -> coe C_Error_472 (coe v10)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                   -> coe
                                        C_Built_470
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (MAlonzo.Code.Once.Target.d_asmHeader_38
                                              (coe d_archTarget_386 (coe v3)))
                                           (d_compileAllWithTarget_424
                                              (coe d_archTarget_386 (coe v3)) (coe v10)))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
