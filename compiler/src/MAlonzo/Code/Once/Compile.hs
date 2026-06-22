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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Escape
import qualified MAlonzo.Code.Once.IR
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
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.RiscV64
import qualified MAlonzo.Code.Once.Target.X86Z45Z32
import qualified MAlonzo.Code.Once.Target.X86Z45Z64
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Raw

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
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_wrapMainAsEntry_8 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
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
      (coe MAlonzo.Code.Once.IR.C_apply_96)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v0
         (coe MAlonzo.Code.Once.IR.C_terminal_74)
         (coe MAlonzo.Code.Once.IR.C_Stack_6))
-- Once.Compile.maybeWrapMain
d_maybeWrapMain_18 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
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
-- Once.Compile.compileFunBody-aux
d_compileFunBody'45'aux_46 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_306 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody'45'aux_46 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_compileFunBody'45'aux_46 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_compileFunBody'45'aux_46 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_306 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody'45'aux_46 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v3)
                (coe
                   MAlonzo.Code.Once.Optimize.d_optimize_4106
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du_'10214'_'10215''7580'_38
                      (coe v1))
                   v7
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_108 (coe v1)
                      (coe v7) (coe v2)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_13380 (coe v0)
                         (coe v1) (coe v7) (coe v5)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                            (coe v4))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                            (coe v4))
                         (coe (0 :: Integer)) (coe v10))))
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_108 (coe v1)
                   (coe v7) (coe v2)
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_13380 (coe v0)
                      (coe v1) (coe v7) (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                         (coe v4))
                      (coe (0 :: Integer)) (coe v10))))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_322 v9
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Type error in " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v6
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text)
                      (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_76 (coe v9)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunBody
d_compileFunBody_92 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_92 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_compileFunBody'45'aux_46 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1294
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
            (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
         (coe v7) (coe v6))
-- Once.Compile.compileFun-main-aux
d_compileFun'45'main'45'aux_114 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'main'45'aux_114 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             d_compileFunBody_92 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFun-aux
d_compileFun'45'aux_154 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'aux_154 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             d_compileFun'45'main'45'aux_114 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe d_validateMain_4 (coe v6))
      else coe
             d_compileFunBody_92 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
-- Once.Compile.compileFun
d_compileFun_192 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_192 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_compileFun'45'aux_154 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v5)
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.CompiledFun
d_CompiledFun_210 = ()
data T_CompiledFun_210
  = C_mkCompiledFun_228 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_Type_112 MAlonzo.Code.Once.IR.T_IR_16 Bool
-- Once.Compile.CompiledFun.cfName
d_cfName_220 ::
  T_CompiledFun_210 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_cfName_220 v0
  = case coe v0 of
      C_mkCompiledFun_228 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_222 ::
  T_CompiledFun_210 -> MAlonzo.Code.Once.Type.T_Type_112
d_cfType_222 v0
  = case coe v0 of
      C_mkCompiledFun_228 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_224 :: T_CompiledFun_210 -> MAlonzo.Code.Once.IR.T_IR_16
d_cfIR_224 v0
  = case coe v0 of
      C_mkCompiledFun_228 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIsPrimitive
d_cfIsPrimitive_226 :: T_CompiledFun_210 -> Bool
d_cfIsPrimitive_226 v0
  = case coe v0 of
      C_mkCompiledFun_228 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_230 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_230 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_28
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funType_126 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       d_extendFunCtx_30 (coe d_buildFunCtx_230 (coe v2))
                       (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v1)) (coe v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe d_buildFunCtx_230 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_250 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_136] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_250 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyPolyCtx_46
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.d_pfunName_146 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Parser.d_pfunType_148 (coe v1))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_152 (coe v1))))
             (coe d_buildPolyCtx_250 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType
d_inferType_256 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType_256 v0 v1 v2
  = let v3
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1428
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                    (coe v0) (coe v1))
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v4 v5 v6 v7 v8
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Cannot infer type: " :: Data.Text.Text)
                   (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_76 (coe v4)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.resolveFunType
d_resolveFunType_284 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveFunType_284 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_inferType_256 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.caf-go-wrap
d_caf'45'go'45'wrap_304 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_caf'45'go'45'wrap_304 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   C_mkCompiledFun_228
                   (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v0))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_maybeWrapMain_18
                         (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v0)) (coe v1)
                         (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_maybeWrapMain_18
                         (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v0)) (coe v1)
                         (coe v2)))
                   (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_132 (coe v0)))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.caf-go-cf-aux
d_caf'45'go'45'cf'45'aux_310 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_112 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_caf'45'go'45'cf'45'aux_310 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             d_caf'45'go'45'wrap_304 (coe v4) (coe v7) (coe v9)
             (coe
                d_compileAllFuns'45'go_316 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v5)
                (coe
                   d_extendFunCtx_30 (coe v6)
                   (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v4)) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.caf-go-rf-aux
d_caf'45'go'45'rf'45'aux_314 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_112 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_caf'45'go'45'rf'45'aux_314 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             d_caf'45'go'45'cf'45'aux_310 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v8)
             (coe
                d_compileFun_192 (coe v0) (coe v1) (coe v6) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v4)) (coe v8)
                (coe MAlonzo.Code.Once.Parser.d_funBody_130 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns-go
d_compileAllFuns'45'go_316 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns'45'go_316 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      (:) v6 v7
        -> coe
             d_caf'45'go'45'rf'45'aux_314 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v6) (coe v7) (coe v5)
             (coe
                d_resolveFunType_284 (coe v5) (coe v2)
                (coe MAlonzo.Code.Once.Parser.d_funType_126 (coe v6))
                (coe MAlonzo.Code.Once.Parser.d_funBody_130 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns
d_compileAllFuns_430 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns_430 v0 v1 v2 v3 v4
  = coe
      d_compileAllFuns'45'go_316 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe v2) (coe d_emptyFunCtx_28)
-- Once.Compile.collectSigEffects
d_collectSigEffects_442 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectSigEffects_442 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_collectSigEffects_442 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v4 v5 v6 v7
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20 v8
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("." :: Data.Text.Text) v4))
                                        (coe v9))
                                     (coe d_collectSigEffects_442 (coe v2))
                              _ -> coe v3
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                        (coe v8))
                                     (coe d_collectSigEffects_442 (coe v2))
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileModule
d_compileModule_460 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_460 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v3
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v2) in
                  coe
                    (let v4
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v2)) in
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
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
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
             = MAlonzo.Code.Once.Parser.d_extractFunctions_420
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v3))
                 (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
              -> case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> coe
                          d_compileAllFuns_430 (coe v0) (coe v1) (coe v6)
                          (coe d_buildPolyCtx_250 (coe v7))
                          (coe
                             d_collectSigEffects_442
                             (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v3)))
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_496 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_496
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_32
-- Once.Compile.compileResolvedModule-aux
d_compileResolvedModule'45'aux_498 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule'45'aux_498 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    d_compileAllFuns_430 (coe v0) (coe v1) (coe v5)
                    (coe d_buildPolyCtx_250 (coe v6))
                    (coe
                       d_collectSigEffects_442
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_518 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_518 v0 v1 v2
  = coe
      d_compileResolvedModule'45'aux_498 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_420
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v2))
         (coe v2))
-- Once.Compile.pipeline
d_pipeline_530 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline_530 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Escape.d_escape_148 v0 v1
      (coe
         MAlonzo.Code.Once.Optimize.d_optimize_4106 v0 v1
         (MAlonzo.Code.Once.Surface.Desugar.d_desugar_18
            (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Compile.pipeline-default
d_pipeline'45'default_540 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline'45'default_540 v0 v1
  = coe
      d_pipeline_530 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Compile.pipeline-no-escape
d_pipeline'45'no'45'escape_546 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline'45'no'45'escape_546 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Optimize.d_optimize_4106 v0 v1
      (MAlonzo.Code.Once.Surface.Desugar.d_desugar_18
         (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Compile.pipeline-no-opt
d_pipeline'45'no'45'opt_556 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline'45'no'45'opt_556 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Desugar.d_desugar_18 (coe v0) (coe v1)
-- Once.Compile.archTarget
d_archTarget_558 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Target.T_Target_4
d_archTarget_558 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.d_x86'45'64_84
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.d_x86'45'32_36
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe MAlonzo.Code.Once.Target.RiscV64.d_riscv64_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunWithTarget
d_compileFunWithTarget_560 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_210 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunWithTarget_560 v0 v1 v2
  = let v3 = d_cfIsPrimitive_226 (coe v2) in
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
                         (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_222 (coe v2))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                               (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe d_cfType_222 (coe v2))
                               (coe d_cfIR_224 (coe v2))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Target.d_irToBodies_36 v0 v1
                         (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_222 (coe v2))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                               (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe d_cfType_222 (coe v2))
                               (coe d_cfIR_224 (coe v2)))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe
                         MAlonzo.Code.Once.Target.d_functionPrologue_40 v0
                         (d_cfName_220 (coe v2)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Target.d_irToAsm_30 v0 v1
                               (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_222 (coe v2))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                     (coe d_cfType_222 (coe v2)) (coe d_cfIR_224 (coe v2))))))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Once.Target.d_functionEpilogue_42 (coe v0))
                            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Once.Target.d_irToBodies_36 v0 v1
                                  (coe MAlonzo.Code.Once.Type.C_Unit_122) (d_cfType_222 (coe v2))
                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                                        (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                        (coe d_cfType_222 (coe v2)) (coe d_cfIR_224 (coe v2)))))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                         (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe d_cfType_222 (coe v2))
                         (coe d_cfIR_224 (coe v2))))))
-- Once.Compile.compileAllWithTarget
d_compileAllWithTarget_596 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_210] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAllWithTarget_596 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_606 (coe v0))
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
                  MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_606 (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe ("" :: Data.Text.Text))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe v1)))))
-- Once.Compile._.step
d_step_606 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_210] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_210 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_606 v0 ~v1 v2 v3 = du_step_606 v0 v2 v3
du_step_606 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_210 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_606 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_compileFunWithTarget_560 (coe v0)
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
                     d_compileFunWithTarget_560 (coe v0)
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
                     d_compileFunWithTarget_560 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                     (coe v2))))))
-- Once.Compile.Stage
d_Stage_628 = ()
data T_Stage_628 = C_Parse_630 | C_Check_632 | C_Build_634
-- Once.Compile.CompileResult
d_CompileResult_636 = ()
data T_CompileResult_636
  = C_Parsed_638 [MAlonzo.Code.Once.Parser.T_FunInfo_112]
                 [MAlonzo.Code.Once.Parser.T_PolyFunInfo_136] |
    C_Checked_640 [T_CompiledFun_210] |
    C_Built_642 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_644 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.showFunInfo
d_showFunInfo_646 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_646 v0
  = let v1 = MAlonzo.Code.Once.Parser.d_funType_126 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_124 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" : " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_202 (coe v2)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_124 (coe v0))
                (" : <inferred>" :: Data.Text.Text)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.showPolyFunInfo
d_showPolyFunInfo_660 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_660 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_146 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_464
            (coe MAlonzo.Code.Once.Parser.d_pfunType_148 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_664 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_664 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_646 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_664 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_646 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_672 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_136] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_672 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_660 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_672 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_660 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_680 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_628 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_636
d_compile_680 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (let v5
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v4) in
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
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
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
                              = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v4) in
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
                                                                                 MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
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
                              = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634 (coe v4) in
                        coe
                          (let v8
                                 = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_634
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
                                                                                 MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_284
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
                          = MAlonzo.Code.Once.Parser.d_extractFunctions_420
                              (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v7))
                              (coe v7) in
                    coe
                      (case coe v8 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                           -> coe C_Error_644 (coe v9)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                           -> case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                  -> case coe v1 of
                                       C_Parse_630 -> coe C_Parsed_638 (coe v10) (coe v11)
                                       C_Check_632
                                         -> let v12
                                                  = d_compileAllFuns_430
                                                      (coe v0) (coe v2) (coe v10)
                                                      (coe d_buildPolyCtx_250 (coe v11))
                                                      (coe
                                                         d_collectSigEffects_442
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                            (coe v7))) in
                                            coe
                                              (case coe v12 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                                   -> coe C_Error_644 (coe v13)
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                                   -> coe C_Checked_640 (coe v13)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       C_Build_634
                                         -> let v12
                                                  = d_compileAllFuns_430
                                                      (coe v0) (coe v2) (coe v10)
                                                      (coe d_buildPolyCtx_250 (coe v11))
                                                      (coe
                                                         d_collectSigEffects_442
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                            (coe v7))) in
                                            coe
                                              (case coe v12 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                                   -> coe C_Error_644 (coe v13)
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                                   -> coe
                                                        C_Built_642
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           (MAlonzo.Code.Once.Target.d_asmHeader_38
                                                              (coe d_archTarget_558 (coe v3)))
                                                           (d_compileAllWithTarget_596
                                                              (coe d_archTarget_558 (coe v3))
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
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (")" :: Data.Text.Text)
                                     (coe MAlonzo.Code.Once.Parser.du_tvarHint_80 (coe v5)))) in
                     coe (coe C_Error_644 (coe v8))))))
-- Once.Compile.cfm-build-emit
d_cfm'45'build'45'emit_748 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_636
d_cfm'45'build'45'emit_748 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe C_Error_644 (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             C_Built_642
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.d_asmHeader_38
                   (coe d_archTarget_558 (coe v0)))
                (d_compileAllWithTarget_596
                   (coe d_archTarget_558 (coe v0)) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-check-emit
d_cfm'45'check'45'emit_760 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_636
d_cfm'45'check'45'emit_760 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_Error_644 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe C_Checked_640 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-stage-aux
d_cfm'45'stage'45'aux_766 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_628 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_136] -> T_CompileResult_636
d_cfm'45'stage'45'aux_766 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      C_Parse_630 -> coe C_Parsed_638 (coe v5) (coe v6)
      C_Check_632
        -> coe
             d_cfm'45'check'45'emit_760
             (coe
                d_compileAllFuns_430 (coe v0) (coe v2) (coe v5)
                (coe d_buildPolyCtx_250 (coe v6))
                (coe
                   d_collectSigEffects_442
                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v4))))
      C_Build_634
        -> coe
             d_cfm'45'build'45'emit_748 (coe v3)
             (coe
                d_compileAllFuns_430 (coe v0) (coe v2) (coe v5)
                (coe d_buildPolyCtx_250 (coe v6))
                (coe
                   d_collectSigEffects_442
                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-ef-aux
d_cfm'45'ef'45'aux_804 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_628 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_636
d_cfm'45'ef'45'aux_804 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe C_Error_644 (coe v6)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d_cfm'45'stage'45'aux_766 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFromModule
d_compileFromModule_832 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_628 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  T_CompileResult_636
d_compileFromModule_832 v0 v1 v2 v3 v4
  = coe
      d_cfm'45'ef'45'aux_804 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_420
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v4))
         (coe v4))
