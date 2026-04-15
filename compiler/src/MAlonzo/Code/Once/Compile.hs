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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Escape
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Surface.Desugar
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Target.X86Z45Z64
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Compile.validateMain
d_validateMain_4 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_validateMain_4 v0
  = let v1
          = coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
              (coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                 ("main must have type Eff Unit A, but got: " :: Data.Text.Text)
                 (MAlonzo.Code.Once.Type.d_showType_130 (coe v0))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Unit_44
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> coe v1
         _ -> coe v1)
-- Once.Compile.compileFunBody
d_compileFunBody_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_12 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabImpl_1128
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_ctxWithImportsAndSelf_390
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0)
                 (coe v1))
              (coe v2) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_352 v4 v5 v6 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v8 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v5))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v5)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                     -> if coe v9
                          then let v11 = seq (coe v10) (coe v3) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_352 v12 v13 v14 v15
                                      -> coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                           (coe
                                              MAlonzo.Code.Once.Optimize.d_optimize_946
                                              (coe MAlonzo.Code.Once.Type.C_Unit_44) v1
                                              (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                 (coe (0 :: Integer))
                                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                 (coe v1) (coe v12)))
                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_354 v12
                                      -> coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("Type error in " :: Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    (": " :: Data.Text.Text) v12)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v11
                                      = seq
                                          (coe v10)
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_354
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("Expression nesting depth exceeds verified limit.\n"
                                                 ::
                                                 Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("  Depth encountered: " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         ("\n" :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("  Proven depth limit: 7\n"
                                                             ::
                                                             Data.Text.Text)
                                                            ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                             ::
                                                             Data.Text.Text))))))) in
                                coe
                                  (case coe v11 of
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_352 v12 v13 v14 v15
                                       -> coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                            (coe
                                               MAlonzo.Code.Once.Optimize.d_optimize_946
                                               (coe MAlonzo.Code.Once.Type.C_Unit_44) v1
                                               (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                  (coe v1) (coe v12)))
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_354 v12
                                       -> coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               ("Type error in " :: Data.Text.Text)
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                                                  (coe
                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                     (": " :: Data.Text.Text) v12)))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_354 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_352 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Once.Optimize.d_optimize_946
                          (coe MAlonzo.Code.Once.Type.C_Unit_44) v1
                          (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v1)
                             (coe v5)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_354 v5
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Type error in " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (": " :: Data.Text.Text) v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.compileFun
d_compileFun_44 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_44 v0 v1 v2
  = let v3 = d_validateMain_4 (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> coe d_compileFunBody_12 (coe v0) (coe v1) (coe v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.CompiledFun
d_CompiledFun_94 = ()
data T_CompiledFun_94
  = C_mkCompiledFun_108 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_Type_34 MAlonzo.Code.Once.CCC.IR.T_IR_12
-- Once.Compile.CompiledFun.cfName
d_cfName_102 ::
  T_CompiledFun_94 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_cfName_102 v0
  = case coe v0 of
      C_mkCompiledFun_108 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_104 ::
  T_CompiledFun_94 -> MAlonzo.Code.Once.Type.T_Type_34
d_cfType_104 v0
  = case coe v0 of
      C_mkCompiledFun_108 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_106 :: T_CompiledFun_94 -> MAlonzo.Code.Once.CCC.IR.T_IR_12
d_cfIR_106 v0
  = case coe v0 of
      C_mkCompiledFun_108 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileAllFuns
d_compileAllFuns_110 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_38] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFuns_110 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v0)
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funType_50 (coe v1) in
           coe
             (let v4
                    = d_validateMain_4
                        (coe MAlonzo.Code.Once.Parser.d_funType_50 (coe v1)) in
              coe
                (let v5 = MAlonzo.Code.Once.Parser.d_funName_48 (coe v1) in
                 coe
                   (let v6 = MAlonzo.Code.Once.Parser.d_funBody_54 (coe v1) in
                    coe
                      (case coe v4 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                           -> case coe v4 of
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v4
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                                  -> let v9 = d_compileAllFuns_110 (coe v2) in
                                     coe
                                       (case coe v9 of
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> coe v9
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                            -> coe
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       C_mkCompiledFun_108
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.d_funName_48
                                                          (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.d_funType_50
                                                          (coe v1))
                                                       (coe v8))
                                                    (coe v10))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                           -> let v8 = d_compileFunBody_12 (coe v5) (coe v3) (coe v6) in
                              coe
                                (case coe v8 of
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                                     -> let v10 = d_compileAllFuns_110 (coe v2) in
                                        coe
                                          (case coe v10 of
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                               -> coe v10
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                               -> coe
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          C_mkCompiledFun_108
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.d_funName_48
                                                             (coe v1))
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.d_funType_50
                                                             (coe v1))
                                                          (coe v9))
                                                       (coe v11))
                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                   _ -> MAlonzo.RTE.mazUnreachableError)
                         _ -> MAlonzo.RTE.mazUnreachableError))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileModule
d_compileModule_152 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_152 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Core.d_expect_162
              (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_64) in
    coe
      (let v2
             = MAlonzo.Code.Once.Parser.Lexer.d_tokenize_202
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0) in
       coe
         (let v3
                = MAlonzo.Code.Once.Parser.Core.d_expect_162
                    (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_64)
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenize_202
                       (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)) in
          coe
            (case coe v3 of
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                 -> case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                        -> let v7
                                 = coe
                                     MAlonzo.Code.Once.Parser.Core.du_many_280 (coe v1) (coe v6) in
                           coe
                             (case coe v7 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                  -> case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                         -> let v11
                                                  = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240
                                                      (coe v10) in
                                            coe
                                              (case coe v11 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                   -> case coe v12 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                          -> let v15
                                                                   = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                                                       (coe v13) (coe v14) in
                                                             coe
                                                               (case coe v15 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                    -> case coe v16 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                           -> let v19
                                                                                    = coe
                                                                                        MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                        (coe v17) in
                                                                              coe
                                                                                (coe
                                                                                   d_compileAllFuns_110
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                         (coe v19))
                                                                                      (coe v19)))
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> let v16
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                                       coe
                                                                         (coe
                                                                            d_compileAllFuns_110
                                                                            (coe
                                                                               MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                  (coe v16))
                                                                               (coe v16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v12
                                                            = coe
                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                                      coe
                                                        (let v13
                                                               = coe
                                                                   MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                   (coe v12) in
                                                         coe
                                                           (coe
                                                              d_compileAllFuns_110
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                    (coe v13))
                                                                 (coe v13))))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v8
                                           = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240
                                               (coe v6) in
                                     coe
                                       (case coe v8 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                            -> case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                   -> let v12
                                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                                                (coe v10) (coe v11) in
                                                      coe
                                                        (case coe v12 of
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                             -> case coe v13 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                    -> let v16
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                 (coe v14) in
                                                                       coe
                                                                         (coe
                                                                            d_compileAllFuns_110
                                                                            (coe
                                                                               MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                  (coe v16))
                                                                               (coe v16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> let v13
                                                                      = coe
                                                                          MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                                coe
                                                                  (coe
                                                                     d_compileAllFuns_110
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                        (coe
                                                                           MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                           (coe v13))
                                                                        (coe v13)))
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v9
                                                     = coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                               coe
                                                 (let v10
                                                        = coe
                                                            MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                            (coe v9) in
                                                  coe
                                                    (coe
                                                       d_compileAllFuns_110
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                             (coe v10))
                                                          (coe v10))))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError
               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                 -> let v4
                          = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240 (coe v2) in
                    coe
                      (case coe v4 of
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                           -> case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                  -> let v8
                                           = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                               (coe v6) (coe v7) in
                                     coe
                                       (case coe v8 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                            -> case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                   -> let v12
                                                            = coe
                                                                MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                (coe v10) in
                                                      coe
                                                        (coe
                                                           d_compileAllFuns_110
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                              (coe
                                                                 MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                 (coe v12))
                                                              (coe v12)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v9
                                                     = coe
                                                         MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                               coe
                                                 (coe
                                                    d_compileAllFuns_110
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                          (coe v9))
                                                       (coe v9)))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           -> let v5 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                              coe
                                (let v6
                                       = coe
                                           MAlonzo.Code.Once.Parser.Module.C_mkModule_48 (coe v5) in
                                 coe
                                   (coe
                                      d_compileAllFuns_110
                                      (coe
                                         MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                         (coe MAlonzo.Code.Once.Parser.d_extractAliases_18 (coe v6))
                                         (coe v6))))
                         _ -> MAlonzo.RTE.mazUnreachableError)
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Compile.pipeline
d_pipeline_174 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_pipeline_174 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Escape.d_escape_116 v0 v1
      (coe
         MAlonzo.Code.Once.Optimize.d_optimize_946 v0 v1
         (MAlonzo.Code.Once.Surface.Desugar.d_desugar_16
            (coe v0) (coe v1) (coe v2)))
-- Once.Compile.pipeline-no-escape
d_pipeline'45'no'45'escape_182 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_pipeline'45'no'45'escape_182 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Optimize.d_optimize_946 v0 v1
      (MAlonzo.Code.Once.Surface.Desugar.d_desugar_16
         (coe v0) (coe v1) (coe v2))
-- Once.Compile.pipeline-no-opt
d_pipeline'45'no'45'opt_190 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_pipeline'45'no'45'opt_190 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Desugar.d_desugar_16 (coe v0) (coe v1)
-- Once.Compile.Arch
d_Arch_192 = ()
data T_Arch_192 = C_x86'45'64_194
-- Once.Compile.archTarget
d_archTarget_196 ::
  T_Arch_192 -> MAlonzo.Code.Once.Target.T_Target_4
d_archTarget_196 ~v0 = du_archTarget_196
du_archTarget_196 :: MAlonzo.Code.Once.Target.T_Target_4
du_archTarget_196
  = coe MAlonzo.Code.Once.Target.X86Z45Z64.d_x86'45'64_22
-- Once.Compile.compileFunWithTarget
d_compileFunWithTarget_198 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  T_CompiledFun_94 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileFunWithTarget_198 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe
         MAlonzo.Code.Once.Target.d_functionPrologue_26 v0
         (d_cfName_102 (coe v1)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Once.Target.d_irToAsm_22 v0
            (coe MAlonzo.Code.Once.Type.C_Unit_44) (d_cfType_104 (coe v1))
            (d_cfIR_106 (coe v1)))
         (MAlonzo.Code.Once.Target.d_functionEpilogue_28 (coe v0)))
-- Once.Compile.compileAllWithTarget
d_compileAllWithTarget_204 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_94] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAllWithTarget_204 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              (d_compileFunWithTarget_198 (coe v0) (coe v1))))
      (coe ("" :: Data.Text.Text))
-- Once.Compile.compileWith
d_compileWith_212 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileWith_212 v0 v1
  = let v2
          = MAlonzo.Code.Once.Parser.Core.d_expect_162
              (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_64) in
    coe
      (let v3
             = MAlonzo.Code.Once.Parser.Lexer.d_tokenize_202
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1) in
       coe
         (let v4
                = MAlonzo.Code.Once.Parser.Core.d_expect_162
                    (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_64)
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenize_202
                       (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)) in
          coe
            (case coe v4 of
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                 -> case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                        -> let v8
                                 = coe
                                     MAlonzo.Code.Once.Parser.Core.du_many_280 (coe v2) (coe v7) in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                  -> case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                         -> let v12
                                                  = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240
                                                      (coe v11) in
                                            coe
                                              (case coe v12 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                   -> case coe v13 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                          -> let v16
                                                                   = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                                                       (coe v14) (coe v15) in
                                                             coe
                                                               (case coe v16 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                    -> case coe v17 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                           -> let v20
                                                                                    = let v20
                                                                                            = coe
                                                                                                MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                                (coe
                                                                                                   v18) in
                                                                                      coe
                                                                                        (d_compileAllFuns_110
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                                 (coe
                                                                                                    v20))
                                                                                              (coe
                                                                                                 v20))) in
                                                                              coe
                                                                                (case coe v20 of
                                                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                                                                                     -> coe v20
                                                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                                                                                     -> coe
                                                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                             (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                                                (coe
                                                                                                   v0))
                                                                                             (coe
                                                                                                d_compileAllWithTarget_204
                                                                                                v0
                                                                                                v21))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> let v17
                                                                             = let v17
                                                                                     = coe
                                                                                         MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                                               coe
                                                                                 (d_compileAllFuns_110
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                          (coe v17))
                                                                                       (coe
                                                                                          v17))) in
                                                                       coe
                                                                         (case coe v17 of
                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                                                              -> coe v17
                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                                                              -> coe
                                                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                      (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                                         (coe v0))
                                                                                      (coe
                                                                                         d_compileAllWithTarget_204
                                                                                         v0 v18))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v13
                                                            = let v13
                                                                    = coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                                              coe
                                                                (let v14
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                           (coe v13) in
                                                                 coe
                                                                   (d_compileAllFuns_110
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                         (coe
                                                                            MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                            (coe v14))
                                                                         (coe v14)))) in
                                                      coe
                                                        (case coe v13 of
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                                             -> coe v13
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                                             -> coe
                                                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                  (coe
                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                     (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                        (coe v0))
                                                                     (coe
                                                                        d_compileAllWithTarget_204
                                                                        v0 v14))
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v9
                                           = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240
                                               (coe v7) in
                                     coe
                                       (case coe v9 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                            -> case coe v10 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                   -> let v13
                                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                                                (coe v11) (coe v12) in
                                                      coe
                                                        (case coe v13 of
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                             -> case coe v14 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                    -> let v17
                                                                             = let v17
                                                                                     = coe
                                                                                         MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                         (coe
                                                                                            v15) in
                                                                               coe
                                                                                 (d_compileAllFuns_110
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                          (coe v17))
                                                                                       (coe
                                                                                          v17))) in
                                                                       coe
                                                                         (case coe v17 of
                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                                                              -> coe v17
                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                                                              -> coe
                                                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                      (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                                         (coe v0))
                                                                                      (coe
                                                                                         d_compileAllWithTarget_204
                                                                                         v0 v18))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> let v14
                                                                      = let v14
                                                                              = coe
                                                                                  MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                                        coe
                                                                          (d_compileAllFuns_110
                                                                             (coe
                                                                                MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                                   (coe v14))
                                                                                (coe v14))) in
                                                                coe
                                                                  (case coe v14 of
                                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                                                       -> coe v14
                                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                                                       -> coe
                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                               (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                                  (coe v0))
                                                                               (coe
                                                                                  d_compileAllWithTarget_204
                                                                                  v0 v15))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v10
                                                     = let v10
                                                             = coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                                       coe
                                                         (let v11
                                                                = coe
                                                                    MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                    (coe v10) in
                                                          coe
                                                            (d_compileAllFuns_110
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                     (coe v11))
                                                                  (coe v11)))) in
                                               coe
                                                 (case coe v10 of
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                                      -> coe v10
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                                      -> coe
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                 (coe v0))
                                                              (coe
                                                                 d_compileAllWithTarget_204 v0 v11))
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError
               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                 -> let v5
                          = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240 (coe v3) in
                    coe
                      (case coe v5 of
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                           -> case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                  -> let v9
                                           = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                               (coe v7) (coe v8) in
                                     coe
                                       (case coe v9 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                            -> case coe v10 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                   -> let v13
                                                            = let v13
                                                                    = coe
                                                                        MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                        (coe v11) in
                                                              coe
                                                                (d_compileAllFuns_110
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                         (coe v13))
                                                                      (coe v13))) in
                                                      coe
                                                        (case coe v13 of
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                                             -> coe v13
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                                             -> coe
                                                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                  (coe
                                                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                     (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                        (coe v0))
                                                                     (coe
                                                                        d_compileAllWithTarget_204
                                                                        v0 v14))
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v10
                                                     = let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                       coe
                                                         (d_compileAllFuns_110
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                                  (coe v10))
                                                               (coe v10))) in
                                               coe
                                                 (case coe v10 of
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                                      -> coe v10
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                                      -> coe
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              (MAlonzo.Code.Once.Target.d_asmHeader_24
                                                                 (coe v0))
                                                              (coe
                                                                 d_compileAllWithTarget_204 v0 v11))
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           -> let v6
                                    = let v6 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                      coe
                                        (let v7
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                   (coe v6) in
                                         coe
                                           (d_compileAllFuns_110
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_extractAliases_18
                                                    (coe v7))
                                                 (coe v7)))) in
                              coe
                                (case coe v6 of
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v6
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                                     -> coe
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (MAlonzo.Code.Once.Target.d_asmHeader_24 (coe v0))
                                             (coe d_compileAllWithTarget_204 v0 v7))
                                   _ -> MAlonzo.RTE.mazUnreachableError)
                         _ -> MAlonzo.RTE.mazUnreachableError)
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Compile.compile
d_compile_234 ::
  T_Arch_192 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compile_234 ~v0 = du_compile_234
du_compile_234 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compile_234 = coe d_compileWith_212 (coe du_archTarget_196)
