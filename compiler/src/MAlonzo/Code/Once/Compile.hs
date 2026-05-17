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
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
                 (MAlonzo.Code.Once.Type.d_showType_194 (coe v0))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Unit_118
                  -> case coe v3 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> case coe v6 of
                                     MAlonzo.Code.Once.Type.C_eff_36
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Type.C_Unit_118
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
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
            (coe MAlonzo.Code.Once.Type.C_Unit_118)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_eff_36))
            (coe MAlonzo.Code.Once.Type.C_Unit_118))
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_352)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v0
         (coe MAlonzo.Code.Once.CCC.IR.C_terminal_330)
         (coe MAlonzo.Code.Once.CCC.IR.C_Stack_260))
-- Once.Compile.maybeWrapMain
d_maybeWrapMain_18 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
                 -> case coe v4 of
                      MAlonzo.Code.Once.Type.C_Unit_118
                        -> case coe v5 of
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                               -> case coe v7 of
                                    MAlonzo.Code.Once.Type.C_Many_10
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.Type.C_eff_36
                                             -> case coe v6 of
                                                  MAlonzo.Code.Once.Type.C_Unit_118
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendFunCtx_30 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.Compile.compileFunBody
d_compileFunBody_42 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_42 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_936
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_184
                    (coe v1) (coe v2) (coe v3) (coe v4))
                 (coe v5) (coe v4)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_276 v7 v8 v9 v10
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Optimize.d_optimize_4026
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_'10214'_'10215''7580'_44
                         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8))
                      v4
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_114
                         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v4)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_11222
                            (coe (0 :: Integer))
                            (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v4) (coe v2)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                               (coe v1))
                            (coe (0 :: Integer)) (coe v8))))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_114
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v4)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_11222
                         (coe (0 :: Integer))
                         (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v4) (coe v2)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                            (coe v1))
                         (coe (0 :: Integer)) (coe v8))))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_278 v7
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Type error in " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (": " :: Data.Text.Text)
                         (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_76 (coe v7)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.compileFun
d_compileFun_96 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_96 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v6 ->
                    coe
                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                      (coe v3))
                 (coe
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                    (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                    (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                       ("main" :: Data.Text.Text)))) in
    coe
      (if coe v6
         then let v7 = d_validateMain_4 (coe v4) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                     -> coe
                          d_compileFunBody_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         else coe
                d_compileFunBody_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5))
-- Once.Compile.CompiledFun
d_CompiledFun_168 = ()
data T_CompiledFun_168
  = C_mkCompiledFun_186 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.CCC.IR.T_IR_274
                        Bool
-- Once.Compile.CompiledFun.cfName
d_cfName_178 ::
  T_CompiledFun_168 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_cfName_178 v0
  = case coe v0 of
      C_mkCompiledFun_186 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_180 ::
  T_CompiledFun_168 -> MAlonzo.Code.Once.Type.T_Type_108
d_cfType_180 v0
  = case coe v0 of
      C_mkCompiledFun_186 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_182 ::
  T_CompiledFun_168 -> MAlonzo.Code.Once.CCC.IR.T_IR_274
d_cfIR_182 v0
  = case coe v0 of
      C_mkCompiledFun_186 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIsPrimitive
d_cfIsPrimitive_184 :: T_CompiledFun_168 -> Bool
d_cfIsPrimitive_184 v0
  = case coe v0 of
      C_mkCompiledFun_186 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_188 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_188 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_28
      (:) v1 v2
        -> coe
             d_extendFunCtx_30 (coe d_buildFunCtx_188 (coe v2))
             (coe MAlonzo.Code.Once.Parser.d_funName_96 (coe v1))
             (coe MAlonzo.Code.Once.Parser.d_funType_98 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_194 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_108] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_194 v0
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
             (coe d_buildPolyCtx_194 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns
d_compileAllFuns_200 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns_200 v0 v1 v2
  = coe du_go_212 (coe v0) (coe v2) (coe v1) (coe d_emptyFunCtx_28)
-- Once.Compile._.go
d_go_212 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_212 v0 ~v1 v2 v3 v4 = du_go_212 v0 v2 v3 v4
du_go_212 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_212 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v2)
      (:) v4 v5
        -> let v6 = MAlonzo.Code.Once.Parser.d_funName_96 (coe v4) in
           coe
             (let v7
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                           erased
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                (coe MAlonzo.Code.Once.Parser.d_funName_96 (coe v4)))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                              (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                 (MAlonzo.Code.Once.Parser.d_funName_96 (coe v4)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                 ("main" :: Data.Text.Text)))) in
              coe
                (let v8 = MAlonzo.Code.Once.Parser.d_funType_98 (coe v4) in
                 coe
                   (let v9 = MAlonzo.Code.Once.Parser.d_funBody_102 (coe v4) in
                    coe
                      (if coe v7
                         then let v10 = d_validateMain_4 (coe v8) in
                              coe
                                (case coe v10 of
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                     -> case coe v10 of
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12 -> coe v10
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                            -> let v13
                                                     = coe
                                                         du_go_212 (coe v0) (coe v1) (coe v5)
                                                         (coe
                                                            d_extendFunCtx_30 (coe v3)
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funName_96
                                                               (coe v4))
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funType_98
                                                               (coe v4))) in
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
                                                                 C_mkCompiledFun_186
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_96
                                                                    (coe v4))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                    (coe
                                                                       d_maybeWrapMain_18
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funName_96
                                                                          (coe v4))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funType_98
                                                                          (coe v4))
                                                                       (coe v12)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                    (coe
                                                                       d_maybeWrapMain_18
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funName_96
                                                                          (coe v4))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funType_98
                                                                          (coe v4))
                                                                       (coe v12)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funIsPrimitive_104
                                                                    (coe v4)))
                                                              (coe v14))
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                     -> let v12
                                              = d_compileFunBody_42
                                                  (coe v0) (coe v3) (coe v1) (coe v6) (coe v8)
                                                  (coe v9) in
                                        coe
                                          (case coe v12 of
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                               -> coe v12
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                               -> let v14
                                                        = coe
                                                            du_go_212 (coe v0) (coe v1) (coe v5)
                                                            (coe
                                                               d_extendFunCtx_30 (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_funName_96
                                                                  (coe v4))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_funType_98
                                                                  (coe v4))) in
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
                                                                    C_mkCompiledFun_186
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.d_funName_96
                                                                       (coe v4))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                       (coe
                                                                          d_maybeWrapMain_18
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funName_96
                                                                             (coe v4))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funType_98
                                                                             (coe v4))
                                                                          (coe v13)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                       (coe
                                                                          d_maybeWrapMain_18
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funName_96
                                                                             (coe v4))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funType_98
                                                                             (coe v4))
                                                                          (coe v13)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.d_funIsPrimitive_104
                                                                       (coe v4)))
                                                                 (coe v15))
                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                   _ -> MAlonzo.RTE.mazUnreachableError)
                         else (let v10
                                     = d_compileFunBody_42
                                         (coe v0) (coe v3) (coe v1) (coe v6) (coe v8) (coe v9) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11 -> coe v10
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                      -> let v12
                                               = coe
                                                   du_go_212 (coe v0) (coe v1) (coe v5)
                                                   (coe
                                                      d_extendFunCtx_30 (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funName_96
                                                         (coe v4))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funType_98
                                                         (coe v4))) in
                                         coe
                                           (case coe v12 of
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                                -> coe v12
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                                -> coe
                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           C_mkCompiledFun_186
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_funName_96
                                                              (coe v4))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                              (coe
                                                                 d_maybeWrapMain_18
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_96
                                                                    (coe v4))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funType_98
                                                                    (coe v4))
                                                                 (coe v11)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_maybeWrapMain_18
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_96
                                                                    (coe v4))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funType_98
                                                                    (coe v4))
                                                                 (coe v11)))
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_funIsPrimitive_104
                                                              (coe v4)))
                                                        (coe v13))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileModule
d_compileModule_270 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_270 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v2
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v1) in
                  coe
                    (let v3
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v1)) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                            -> case coe v4 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                   -> let v7
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v6) in
                                      coe
                                        (let v8
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v2) in
                                         coe
                                           (case coe v7 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                -> case coe v9 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                              -> let v14
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                           (coe v12) in
                                                                 coe
                                                                   (case coe v14 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v10)
                                                                                       (coe v15))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v17)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v18)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v13))
                                                                                             (coe
                                                                                                v8))))
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
                                                        (coe v6) (coe v8))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v4 v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                                          (coe (0 :: Integer)) (coe v2))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe
      (let v3
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
                          d_compileAllFuns_200 (coe v0) (coe v5)
                          (coe d_buildPolyCtx_194 (coe v6))
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_300 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_300
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_32
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_302 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_302 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.d_extractFunctions_156
              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v1))
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       d_compileAllFuns_200 (coe v0) (coe v4)
                       (coe d_buildPolyCtx_194 (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.pipeline
d_pipeline_322 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline_322 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Escape.d_escape_126 v0 v1
      (coe
         MAlonzo.Code.Once.Optimize.d_optimize_4026 v0 v1
         (MAlonzo.Code.Once.Surface.Desugar.d_desugar_18
            (coe v0) (coe v1) (coe v2)))
-- Once.Compile.pipeline-no-escape
d_pipeline'45'no'45'escape_330 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline'45'no'45'escape_330 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Optimize.d_optimize_4026 v0 v1
      (MAlonzo.Code.Once.Surface.Desugar.d_desugar_18
         (coe v0) (coe v1) (coe v2))
-- Once.Compile.pipeline-no-opt
d_pipeline'45'no'45'opt_338 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_pipeline'45'no'45'opt_338 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Desugar.d_desugar_18 (coe v0) (coe v1)
-- Once.Compile.Arch
d_Arch_340 = ()
data T_Arch_340 = C_x86'45'64_342 | C_x86'45'32_344 | C_riscv64_346
-- Once.Compile.archTarget
d_archTarget_348 ::
  T_Arch_340 -> MAlonzo.Code.Once.Target.T_Target_4
d_archTarget_348 v0
  = case coe v0 of
      C_x86'45'64_342
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.d_x86'45'64_84
      C_x86'45'32_344
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.d_x86'45'32_36
      C_riscv64_346 -> coe MAlonzo.Code.Once.Target.RiscV64.d_riscv64_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunWithTarget
d_compileFunWithTarget_350 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_168 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunWithTarget_350 v0 v1 v2
  = let v3 = d_cfIsPrimitive_184 (coe v2) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe ("" :: Data.Text.Text))
         else coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Target.d_irToAsm_28 v0 v1
                      (coe MAlonzo.Code.Once.Type.C_Unit_118) (d_cfType_180 (coe v2))
                      (d_cfIR_182 (coe v2))))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (coe
                      MAlonzo.Code.Once.Target.d_functionPrologue_38 v0
                      (d_cfName_178 (coe v2)))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Once.Target.d_irToAsm_28 v0 v1
                            (coe MAlonzo.Code.Once.Type.C_Unit_118) (d_cfType_180 (coe v2))
                            (d_cfIR_182 (coe v2))))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Once.Target.d_functionEpilogue_40 (coe v0))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Target.d_irToBodies_34 v0 v1
                               (coe MAlonzo.Code.Once.Type.C_Unit_118) (d_cfType_180 (coe v2))
                               (d_cfIR_182 (coe v2))))))))
-- Once.Compile.compileAllWithTarget
d_compileAllWithTarget_382 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_168] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAllWithTarget_382 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_392 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            (coe ("" :: Data.Text.Text)))
         (coe v1))
-- Once.Compile._.step
d_step_392 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_168] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_168 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_392 v0 ~v1 v2 v3 = du_step_392 v0 v2 v3
du_step_392 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_168 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_392 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_compileFunWithTarget_350 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)) (coe v2)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_compileFunWithTarget_350 (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)) (coe v2))))
-- Once.Compile.Stage
d_Stage_408 = ()
data T_Stage_408 = C_Parse_410 | C_Check_412 | C_Build_414
-- Once.Compile.CompileResult
d_CompileResult_416 = ()
data T_CompileResult_416
  = C_Parsed_418 [MAlonzo.Code.Once.Parser.T_FunInfo_84]
                 [MAlonzo.Code.Once.Parser.T_PolyFunInfo_108] |
    C_Checked_420 [T_CompiledFun_168] |
    C_Built_422 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_424 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.showFunInfo
d_showFunInfo_426 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_426 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_funName_96 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showType_194
            (coe MAlonzo.Code.Once.Parser.d_funType_98 (coe v0))))
-- Once.Compile.showPolyFunInfo
d_showPolyFunInfo_430 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_430 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_118 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_456
            (coe MAlonzo.Code.Once.Parser.d_pfunType_120 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_434 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_84] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_434 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_426 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_434 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_426 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_442 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_108] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_442 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_430 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_442 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_430 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_450 ::
  T_Stage_408 ->
  Bool ->
  T_Arch_340 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_416
d_compile_450 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (let v4
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v3) in
                  coe
                    (let v5
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_398
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v3)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> let v9
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v8) in
                                      coe
                                        (let v10
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v4) in
                                         coe
                                           (case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                              -> let v16
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                           (coe v14) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                        -> case coe v18 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v12)
                                                                                       (coe v17))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v19)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v20)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v15))
                                                                                             (coe
                                                                                                v10))))
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
                                                        (coe v8) (coe v10))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v6 v7 -> addInt (coe (1 :: Integer)) (coe v7)))
                                          (coe (0 :: Integer)) (coe v4))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe
      (let v5
             = MAlonzo.Code.Once.Parser.d_allTrailing_18
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (let v5
                              = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v3) in
                        coe
                          (let v6
                                 = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_398
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           v3)) in
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
                                                                                             (coe
                                                                                                v13)
                                                                                             (coe
                                                                                                v18))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v20)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                                (coe
                                                                                                   v21)
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
                                                (coe
                                                   (\ v7 v8 ->
                                                      addInt (coe (1 :: Integer)) (coe v8)))
                                                (coe (0 :: Integer)) (coe v5))))
                                _ -> MAlonzo.RTE.mazUnreachableError))))) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (let v6
                              = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v3) in
                        coe
                          (let v7
                                 = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630
                                        (coe v3)) in
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
                                _ -> MAlonzo.RTE.mazUnreachableError)))) in
          coe
            (if coe v5
               then let v7
                          = MAlonzo.Code.Once.Parser.d_extractFunctions_156
                              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v6))
                              (coe v6) in
                    coe
                      (case coe v7 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                           -> coe C_Error_424 (coe v8)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                           -> case coe v8 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                  -> case coe v0 of
                                       C_Parse_410 -> coe C_Parsed_418 (coe v9) (coe v10)
                                       C_Check_412
                                         -> let v11
                                                  = d_compileAllFuns_200
                                                      (coe v1) (coe v9)
                                                      (coe d_buildPolyCtx_194 (coe v10)) in
                                            coe
                                              (case coe v11 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                                   -> coe C_Error_424 (coe v12)
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                                   -> coe C_Checked_420 (coe v12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       C_Build_414
                                         -> let v11
                                                  = d_compileAllFuns_200
                                                      (coe v1) (coe v9)
                                                      (coe d_buildPolyCtx_194 (coe v10)) in
                                            coe
                                              (case coe v11 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                                   -> coe C_Error_424 (coe v12)
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                                   -> coe
                                                        C_Built_422
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           (MAlonzo.Code.Once.Target.d_asmHeader_36
                                                              (coe d_archTarget_348 (coe v2)))
                                                           (d_compileAllWithTarget_382
                                                              (coe d_archTarget_348 (coe v2))
                                                              (coe v12)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError
                         _ -> MAlonzo.RTE.mazUnreachableError)
               else (let v7
                           = coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("Parse error: unexpected tokens remaining after last parsed decl (starting at: "
                                ::
                                Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (MAlonzo.Code.Once.Parser.d_showTokenPrefix_24 (coe v4))
                                  (")" :: Data.Text.Text)) in
                     coe (coe C_Error_424 (coe v7))))))
-- Once.Compile.compileFromModule
d_compileFromModule_512 ::
  T_Stage_408 ->
  Bool ->
  T_Arch_340 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  T_CompileResult_416
d_compileFromModule_512 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Parser.d_extractFunctions_156
              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v3))
              (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe C_Error_424 (coe v5)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v0 of
                       C_Parse_410 -> coe C_Parsed_418 (coe v6) (coe v7)
                       C_Check_412
                         -> let v8
                                  = d_compileAllFuns_200
                                      (coe v1) (coe v6) (coe d_buildPolyCtx_194 (coe v7)) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                                   -> coe C_Error_424 (coe v9)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                                   -> coe C_Checked_420 (coe v9)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_Build_414
                         -> let v8
                                  = d_compileAllFuns_200
                                      (coe v1) (coe v6) (coe d_buildPolyCtx_194 (coe v7)) in
                            coe
                              (case coe v8 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                                   -> coe C_Error_424 (coe v9)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                                   -> coe
                                        C_Built_422
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (MAlonzo.Code.Once.Target.d_asmHeader_36
                                              (coe d_archTarget_348 (coe v2)))
                                           (d_compileAllWithTarget_382
                                              (coe d_archTarget_348 (coe v2)) (coe v9)))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
