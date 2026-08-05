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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Escape
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Desugar
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.RiscV64
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z32
import qualified MAlonzo.Code.Once.Target.X86Z45Z64
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Principal
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
                 (MAlonzo.Code.Once.Type.d_showType_206 (coe v0))) in
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
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe MAlonzo.Code.Once.Type.C_Unit_122))
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
               (coe MAlonzo.Code.Once.Type.C_Unit_122)))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
            (coe MAlonzo.Code.Once.Type.C_Unit_122)))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v0
         (coe MAlonzo.Code.Once.IR.C_terminal_74)
         (coe MAlonzo.Code.Once.IR.C_Heap_8))
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
-- Once.Compile.directCallIR
d_directCallIR_32 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_directCallIR_32 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Once.Type.C_Unit_122)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v3 v4 v5
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__30
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.C__'8667'__24
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3))
                            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v5)))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v3)))
                      (coe MAlonzo.Code.Once.IR.C_apply_92)
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__30
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                               (coe MAlonzo.Code.Once.Type.C_Unit_122))
                            v1 (coe MAlonzo.Code.Once.IR.C_terminal_74))
                         (coe MAlonzo.Code.Once.IR.C_id_22)
                         (coe MAlonzo.Code.Once.IR.C_Heap_8))))
         _ -> coe v2)
-- Once.Compile.FunCtx
d_FunCtx_46 :: ()
d_FunCtx_46 = erased
-- Once.Compile.emptyFunCtx
d_emptyFunCtx_48 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyFunCtx_48 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Compile.extendFunCtx
d_extendFunCtx_50 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendFunCtx_50 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.Compile.compileFunBody-aux
d_compileFunBody'45'aux_66 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_314 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody'45'aux_66 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_compileFunBody'45'aux_66 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_compileFunBody'45'aux_66 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_314 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody'45'aux_66 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v3)
                (coe
                   MAlonzo.Code.Once.Optimize.d_optimize_4296
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe v1)))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v7))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_108 (coe v1)
                      (coe v7) (coe v2)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_2808
                         (coe v0) (coe v1) (coe v7) (coe v5)
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
                      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_2808
                      (coe v0) (coe v1) (coe v7) (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                         (coe v4))
                      (coe (0 :: Integer)) (coe v10))))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_330 v9
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
                      (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_82 (coe v9)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunBody
d_compileFunBody_112 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_112 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_compileFunBody'45'aux_66 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1608
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
            (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
         (coe v7) (coe v6))
-- Once.Compile.compileFun-main-aux
d_compileFun'45'main'45'aux_134 ::
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
d_compileFun'45'main'45'aux_134 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             d_compileFunBody_112 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFun-aux
d_compileFun'45'aux_174 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'aux_174 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             d_compileFun'45'main'45'aux_134 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7) (coe d_validateMain_4 (coe v6))
      else coe
             d_compileFunBody_112 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
-- Once.Compile.compileFun
d_compileFun_212 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_212 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_compileFun'45'aux_174 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v5)
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.CompiledFun
d_CompiledFun_230 = ()
data T_CompiledFun_230
  = C_mkCompiledFun_248 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                        MAlonzo.Code.Once.Type.T_Type_112 MAlonzo.Code.Once.IR.T_IR_16 Bool
-- Once.Compile.CompiledFun.cfName
d_cfName_240 ::
  T_CompiledFun_230 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_cfName_240 v0
  = case coe v0 of
      C_mkCompiledFun_248 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_242 ::
  T_CompiledFun_230 -> MAlonzo.Code.Once.Type.T_Type_112
d_cfType_242 v0
  = case coe v0 of
      C_mkCompiledFun_248 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_244 :: T_CompiledFun_230 -> MAlonzo.Code.Once.IR.T_IR_16
d_cfIR_244 v0
  = case coe v0 of
      C_mkCompiledFun_248 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIsPrimitive
d_cfIsPrimitive_246 :: T_CompiledFun_230 -> Bool
d_cfIsPrimitive_246 v0
  = case coe v0 of
      C_mkCompiledFun_248 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_250 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_250 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_48
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funType_110 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       d_extendFunCtx_50 (coe d_buildFunCtx_250 (coe v2))
                       (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v1)) (coe v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe d_buildFunCtx_250 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_270 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_270 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyPolyCtx_46
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.d_pfunName_130 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Parser.d_pfunType_132 (coe v1))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_136 (coe v1))))
             (coe d_buildPolyCtx_270 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType-validate
d_inferType'45'validate_276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType'45'validate_276 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1776
                        (coe v0) (coe v1) (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v6 v7 v8 v9
                  -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_330 v6
                  -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType
d_inferType_312 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType_312 v0 v1 v2
  = let v3
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1760
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                    (coe v0) (coe v1))
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v4 v5 v6 v7 v8
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_306 v4
           -> coe
                d_inferType'45'validate_276
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                   (coe v0) (coe v1))
                (coe v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Cannot infer type: " :: Data.Text.Text)
                   (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_82 (coe v4)))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Principal.d_principalGround_2106
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                      (coe v0) (coe v1))
                   (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.resolveFunType
d_resolveFunType_340 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveFunType_340 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_inferType_312 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.caf-go-wrap
d_caf'45'go'45'wrap_360 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_caf'45'go'45'wrap_360 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   C_mkCompiledFun_248
                   (coe
                      MAlonzo.Code.Once.CanonicalName.d_bare_12
                      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_maybeWrapMain_18
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)) (coe v1)
                         (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_maybeWrapMain_18
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)) (coe v1)
                         (coe v2)))
                   (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v0)))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.caf-go-cf-aux
d_caf'45'go'45'cf'45'aux_366 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_caf'45'go'45'cf'45'aux_366 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             d_caf'45'go'45'wrap_360 (coe v4) (coe v7) (coe v9)
             (coe
                d_compileAllFuns'45'go_372 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v5)
                (coe
                   d_extendFunCtx_50 (coe v6)
                   (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4)) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.caf-go-rf-aux
d_caf'45'go'45'rf'45'aux_370 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_caf'45'go'45'rf'45'aux_370 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             d_caf'45'go'45'cf'45'aux_366 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v8)
             (coe
                d_compileFun_212 (coe v0) (coe v1) (coe v6) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4)) (coe v8)
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns-go
d_compileAllFuns'45'go_372 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns'45'go_372 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      (:) v6 v7
        -> coe
             d_caf'45'go'45'rf'45'aux_370 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v6) (coe v7) (coe v5)
             (coe
                d_resolveFunType_340 (coe v5) (coe v2)
                (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v6))
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns
d_compileAllFuns_486 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns_486 v0 v1 v2 v3 v4
  = coe
      d_compileAllFuns'45'go_372 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe v2) (coe d_emptyFunCtx_48)
-- Once.Compile.collectSigEffects
d_collectSigEffects_498 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_collectSigEffects_498 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_collectSigEffects_498 (coe v2) in
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
                                     (coe d_collectSigEffects_498 (coe v2))
                              _ -> coe v3
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                        (coe v8))
                                     (coe d_collectSigEffects_498 (coe v2))
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileModule
d_compileModule_516 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_516 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Parser.Module.d_r_368
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_832 (coe v2)))) in
    coe
      (let v4
             = MAlonzo.Code.Once.Parser.d_extractFunctions_540
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v3))
                 (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
              -> case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> coe
                          d_compileAllFuns_486 (coe v0) (coe v1) (coe v6)
                          (coe d_buildPolyCtx_270 (coe v7))
                          (coe
                             d_collectSigEffects_498
                             (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v3)))
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_552 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_552
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_72
-- Once.Compile.compileResolvedModule-aux
d_compileResolvedModule'45'aux_554 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule'45'aux_554 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    d_compileAllFuns_486 (coe v0) (coe v1) (coe v5)
                    (coe d_buildPolyCtx_270 (coe v6))
                    (coe
                       d_collectSigEffects_498
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_574 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_574 v0 v1 v2
  = coe
      d_compileResolvedModule'45'aux_554 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v2))
         (coe v2))
-- Once.Compile.emittedSyms-cons
d_emittedSyms'45'cons_582 ::
  Bool ->
  T_CompiledFun_230 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedSyms'45'cons_582 v0 v1 v2
  = if coe v0
      then coe v2
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                (coe d_cfName_240 (coe v1)))
             (coe v2)
-- Once.Compile.emittedSyms
d_emittedSyms_592 ::
  [T_CompiledFun_230] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedSyms_592 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_emittedSyms'45'cons_582 (coe d_cfIsPrimitive_246 (coe v1))
             (coe v1) (coe d_emittedSyms_592 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms-aux
d_moduleSyms'45'aux_598 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms'45'aux_598 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_emittedSyms_592 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms
d_moduleSyms_602 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms_602 v0 v1 v2
  = coe
      d_moduleSyms'45'aux_598
      (coe d_compileResolvedModule_574 (coe v0) (coe v1) (coe v2))
-- Once.Compile.pipeline
d_pipeline_614 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline_614 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Escape.d_escape_146
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v0))
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
      (coe
         MAlonzo.Code.Once.Optimize.d_optimize_4296
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v0))
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
         (MAlonzo.Code.Once.Surface.Desugar.d_desugar_22
            (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Compile.pipeline-default
d_pipeline'45'default_624 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline'45'default_624 v0 v1
  = coe
      d_pipeline_614 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Compile.pipeline-no-escape
d_pipeline'45'no'45'escape_630 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline'45'no'45'escape_630 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Optimize.d_optimize_4296
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v0))
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
      (MAlonzo.Code.Once.Surface.Desugar.d_desugar_22
         (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Compile.pipeline-no-opt
d_pipeline'45'no'45'opt_640 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pipeline'45'no'45'opt_640 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Desugar.d_desugar_22 (coe v0) (coe v1)
-- Once.Compile.archTarget
d_archTarget_642 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Target.T_Target_4
d_archTarget_642 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.d_x86'45'64_90
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.d_x86'45'32_90
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe MAlonzo.Code.Once.Target.RiscV64.d_riscv64_92
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunWithTarget
d_compileFunWithTarget_644 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_230 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunWithTarget_644 v0 v1 v2
  = let v3 = d_cfIsPrimitive_246 (coe v2) in
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
                         MAlonzo.Code.Once.Target.d_irToAsm_32 v0 (d_cfName_240 (coe v2)) v1
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                  (coe d_cfIR_244 (coe v2)))))
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                     (coe d_cfIR_244 (coe v2))))))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                        (coe d_cfIR_244 (coe v2)))))
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                           (coe d_cfIR_244 (coe v2))))))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                        (coe d_cfIR_244 (coe v2)))))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Target.d_irToBodies_38 v0 (d_cfName_240 (coe v2))
                         v1
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                  (coe d_cfIR_244 (coe v2)))))
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                     (coe d_cfIR_244 (coe v2))))))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                        (coe d_cfIR_244 (coe v2)))))
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                           (coe d_cfIR_244 (coe v2))))))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                        (coe d_cfIR_244 (coe v2))))))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe
                         MAlonzo.Code.Once.Target.d_functionPrologue_42 v0
                         (d_cfName_240 (coe v2)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Target.d_irToAsm_32 v0 (d_cfName_240 (coe v2)) v1
                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                        (coe d_cfIR_244 (coe v2)))))
                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                           (coe d_cfIR_244 (coe v2))))))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                              (coe d_cfIR_244 (coe v2)))))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                                 (coe d_cfIR_244 (coe v2))))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                              (coe d_cfIR_244 (coe v2)))))))))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Once.Target.d_functionEpilogue_44 (coe v0))
                            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Once.Target.d_irToBodies_38 v0
                                  (d_cfName_240 (coe v2)) v1
                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                           (coe d_cfIR_244 (coe v2)))))
                                  (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                              (coe d_cfIR_244 (coe v2))))))
                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                                 (coe d_cfIR_244 (coe v2)))))
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                 (coe
                                                    d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                                    (coe d_cfIR_244 (coe v2))))))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                                 (coe d_cfIR_244 (coe v2))))))))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_130
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                  (coe d_cfIR_244 (coe v2)))))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                     (coe d_cfIR_244 (coe v2))))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_32 (coe d_cfType_242 (coe v2))
                                  (coe d_cfIR_244 (coe v2)))))))))
-- Once.Compile.compileAllWithTarget
d_compileAllWithTarget_682 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_230] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAllWithTarget_682 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_692 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe ("" :: Data.Text.Text))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
               (coe v1))))
      (coe
         MAlonzo.Code.Once.Target.d_emitArithBlocks_46 v0
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_692 (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe ("" :: Data.Text.Text))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe v1)))))
-- Once.Compile._.step
d_step_692 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_230 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_692 v0 ~v1 v2 v3 = du_step_692 v0 v2 v3
du_step_692 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_230 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_692 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_compileFunWithTarget_644 (coe v0)
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
                     d_compileFunWithTarget_644 (coe v0)
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
                     d_compileFunWithTarget_644 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                     (coe v2))))))
-- Once.Compile.Stage
d_Stage_714 = ()
data T_Stage_714 = C_Parse_716 | C_Check_718 | C_Build_720
-- Once.Compile.CompileResult
d_CompileResult_722 = ()
data T_CompileResult_722
  = C_Parsed_724 [MAlonzo.Code.Once.Parser.T_FunInfo_96]
                 [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] |
    C_Checked_726 [T_CompiledFun_230] |
    C_Built_728 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_730 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.showFunInfo
d_showFunInfo_732 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_732 v0
  = let v1 = MAlonzo.Code.Once.Parser.d_funType_110 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_108 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" : " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_206 (coe v2)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_108 (coe v0))
                (" : <inferred>" :: Data.Text.Text)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.showPolyFunInfo
d_showPolyFunInfo_746 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_120 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_746 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_130 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_468
            (coe MAlonzo.Code.Once.Parser.d_pfunType_132 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_750 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_750 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_732 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_750 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_732 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_758 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_758 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_746 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_758 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_746 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_766 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_714 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_722
d_compile_766 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_306
                       (coe
                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4))
                       (coe
                          MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                             (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)))
                       (\ v5 v6 v7 ->
                          coe
                            MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                            (coe
                               MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                               (coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4))))))
              (coe
                 MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Parser.Module.d_r_368
                       (coe
                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)))))
              (coe
                 MAlonzo.Code.Once.Parser.d_allTrailing_18
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_306
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                             (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4))
                          (coe
                             MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)))
                          (\ v5 v6 v7 ->
                             coe
                               MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                     v4))))))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> coe C_Error_730 (coe v6)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> let v7
                    = MAlonzo.Code.Once.Parser.d_extractFunctions_540
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v6))
                        (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                     -> coe C_Error_730 (coe v8)
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                     -> case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> case coe v1 of
                                 C_Parse_716 -> coe C_Parsed_724 (coe v9) (coe v10)
                                 C_Check_718
                                   -> let v11
                                            = d_compileAllFuns_486
                                                (coe v0) (coe v2) (coe v9)
                                                (coe d_buildPolyCtx_270 (coe v10))
                                                (coe
                                                   d_collectSigEffects_498
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                      (coe v6))) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                             -> coe C_Error_730 (coe v12)
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                             -> coe C_Checked_726 (coe v12)
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 C_Build_720
                                   -> let v11
                                            = d_compileAllFuns_486
                                                (coe v0) (coe v2) (coe v9)
                                                (coe d_buildPolyCtx_270 (coe v10))
                                                (coe
                                                   d_collectSigEffects_498
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                      (coe v6))) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                             -> coe C_Error_730 (coe v12)
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                             -> coe
                                                  C_Built_728
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (MAlonzo.Code.Once.Target.d_asmHeader_40
                                                        (coe d_archTarget_642 (coe v3)))
                                                     (d_compileAllWithTarget_682
                                                        (coe d_archTarget_642 (coe v3)) (coe v12)))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.cfm-build-emit
d_cfm'45'build'45'emit_834 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_722
d_cfm'45'build'45'emit_834 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe C_Error_730 (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             C_Built_728
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.d_asmHeader_40
                   (coe d_archTarget_642 (coe v0)))
                (d_compileAllWithTarget_682
                   (coe d_archTarget_642 (coe v0)) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-check-emit
d_cfm'45'check'45'emit_846 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_722
d_cfm'45'check'45'emit_846 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_Error_730 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe C_Checked_726 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-stage-aux
d_cfm'45'stage'45'aux_852 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_714 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] -> T_CompileResult_722
d_cfm'45'stage'45'aux_852 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      C_Parse_716 -> coe C_Parsed_724 (coe v5) (coe v6)
      C_Check_718
        -> coe
             d_cfm'45'check'45'emit_846
             (coe
                d_compileAllFuns_486 (coe v0) (coe v2) (coe v5)
                (coe d_buildPolyCtx_270 (coe v6))
                (coe
                   d_collectSigEffects_498
                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v4))))
      C_Build_720
        -> coe
             d_cfm'45'build'45'emit_834 (coe v3)
             (coe
                d_compileAllFuns_486 (coe v0) (coe v2) (coe v5)
                (coe d_buildPolyCtx_270 (coe v6))
                (coe
                   d_collectSigEffects_498
                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-ef-aux
d_cfm'45'ef'45'aux_890 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_714 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_722
d_cfm'45'ef'45'aux_890 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe C_Error_730 (coe v6)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    d_cfm'45'stage'45'aux_852 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFromModule
d_compileFromModule_918 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_714 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  T_CompileResult_722
d_compileFromModule_918 v0 v1 v2 v3 v4
  = coe
      d_cfm'45'ef'45'aux_890 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v4))
         (coe v4))
