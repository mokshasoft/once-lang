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

module MAlonzo.Code.Once.CompileX86v3 where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.X86.Emit
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.CompileX86v3.functionPrologue
d_functionPrologue_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionPrologue_4 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (".globl once_" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("\n" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("once_" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                  (":\n" :: Data.Text.Text)))))
-- Once.CompileX86v3.functionEpilogue
d_functionEpilogue_8 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_functionEpilogue_8 = coe ("    ret\n\n" :: Data.Text.Text)
-- Once.CompileX86v3.compileFunctionX86v3
d_compileFunctionX86v3_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunctionX86v3_10 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabImpl_1086
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_ctxWithImportsAndSelf_364
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0)
                 (coe v1))
              (coe v2) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v4 v5 v6 v7
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
                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v12 v13 v14 v15
                                      -> coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (d_functionPrologue_4 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (MAlonzo.Code.Once.Target.X86.Emit.d_programToText_76
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.d_compile'45'ir_62
                                                       (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                       (coe v1)
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.IR.d_fromOnceIR_840
                                                          (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                          (coe v1)
                                                          (coe
                                                             MAlonzo.Code.Once.Optimize.d_optimize_1266
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                             v1
                                                             (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                (coe v1) (coe v12))))))
                                                 d_functionEpilogue_8))
                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v12
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
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328
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
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v12 v13 v14 v15
                                       -> coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (d_functionPrologue_4 (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                  (MAlonzo.Code.Once.Target.X86.Emit.d_programToText_76
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.d_compile'45'ir_62
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                        (coe v1)
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.IR.d_fromOnceIR_840
                                                           (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                           (coe v1)
                                                           (coe
                                                              MAlonzo.Code.Once.Optimize.d_optimize_1266
                                                              (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                              v1
                                                              (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                 (coe v1) (coe v12))))))
                                                  d_functionEpilogue_8))
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v12
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
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (d_functionPrologue_4 (coe v0))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (MAlonzo.Code.Once.Target.X86.Emit.d_programToText_76
                                (coe
                                   MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.d_compile'45'ir_62
                                   (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.CCC.IR.d_fromOnceIR_840
                                      (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Optimize.d_optimize_1266
                                         (coe MAlonzo.Code.Once.Type.C_Unit_34) v1
                                         (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                            (coe (0 :: Integer))
                                            (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                            (coe v1) (coe v5))))))
                             d_functionEpilogue_8))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v5
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
-- Once.CompileX86v3.compileAllFunctions
d_compileAllFunctions_48 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_38] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileAllFunctions_48 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe ("" :: Data.Text.Text))
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funName_48 (coe v1) in
           coe
             (let v4 = MAlonzo.Code.Once.Parser.d_funType_50 (coe v1) in
              coe
                (let v5
                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabImpl_1086
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_ctxWithImportsAndSelf_364
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe MAlonzo.Code.Once.Parser.d_funName_48 (coe v1))
                              (coe MAlonzo.Code.Once.Parser.d_funType_50 (coe v1)))
                           (coe MAlonzo.Code.Once.Parser.d_funBody_54 (coe v1))
                           (coe MAlonzo.Code.Once.Parser.d_funType_50 (coe v1)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v6 v7 v8 v9
                        -> let v10
                                 = coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     (\ v10 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                          (coe v7))
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v7)
                                           (coe (7 :: Integer)))) in
                           coe
                             (case coe v10 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                  -> if coe v11
                                       then let v13 = seq (coe v12) (coe v5) in
                                            coe
                                              (case coe v13 of
                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v14 v15 v16 v17
                                                   -> let v18
                                                            = coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                (d_functionPrologue_4 (coe v3))
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   (MAlonzo.Code.Once.Target.X86.Emit.d_programToText_76
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.d_compile'45'ir_62
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_Unit_34)
                                                                         (coe v4)
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.IR.d_fromOnceIR_840
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Unit_34)
                                                                            (coe v4)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Optimize.d_optimize_1266
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Unit_34)
                                                                               v4
                                                                               (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                                  (coe v4)
                                                                                  (coe v14))))))
                                                                   d_functionEpilogue_8) in
                                                      coe
                                                        (let v19
                                                               = d_compileAllFunctions_48
                                                                   (coe v2) in
                                                         coe
                                                           (case coe v19 of
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                                                                -> coe v19
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                                                                -> coe
                                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                        v18 v20)
                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v14
                                                   -> coe
                                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           ("Type error in " :: Data.Text.Text)
                                                           (coe
                                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                              v3
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                 (": " :: Data.Text.Text) v14)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       else (let v13
                                                   = seq
                                                       (coe v12)
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("Expression nesting depth exceeds verified limit.\n"
                                                              ::
                                                              Data.Text.Text)
                                                             (coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                ("  Depth encountered: "
                                                                 ::
                                                                 Data.Text.Text)
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   (coe
                                                                      MAlonzo.Code.Data.Nat.Show.d_show_56
                                                                      v7)
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
                                               (case coe v13 of
                                                  MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v14 v15 v16 v17
                                                    -> let v18
                                                             = coe
                                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                 (d_functionPrologue_4 (coe v3))
                                                                 (coe
                                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                    (MAlonzo.Code.Once.Target.X86.Emit.d_programToText_76
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.d_compile'45'ir_62
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.C_Unit_34)
                                                                          (coe v4)
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.IR.d_fromOnceIR_840
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Unit_34)
                                                                             (coe v4)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Optimize.d_optimize_1266
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Type.C_Unit_34)
                                                                                v4
                                                                                (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                                   (coe v4)
                                                                                   (coe v14))))))
                                                                    d_functionEpilogue_8) in
                                                       coe
                                                         (let v19
                                                                = d_compileAllFunctions_48
                                                                    (coe v2) in
                                                          coe
                                                            (case coe v19 of
                                                               MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                                                                 -> coe v19
                                                               MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                                                                 -> coe
                                                                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                      (coe
                                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                         v18 v20)
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                  MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v14
                                                    -> coe
                                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("Type error in " :: Data.Text.Text)
                                                            (coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               v3
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                  (": " :: Data.Text.Text) v14)))
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v6
                        -> case coe v5 of
                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_326 v7 v8 v9 v10
                               -> let v11
                                        = coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            (d_functionPrologue_4 (coe v3))
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               (MAlonzo.Code.Once.Target.X86.Emit.d_programToText_76
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Target.X86v3.CodeGen.d_compile'45'ir_62
                                                     (coe MAlonzo.Code.Once.Type.C_Unit_34) (coe v4)
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.IR.d_fromOnceIR_840
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_34)
                                                        (coe v4)
                                                        (coe
                                                           MAlonzo.Code.Once.Optimize.d_optimize_1266
                                                           (coe MAlonzo.Code.Once.Type.C_Unit_34) v4
                                                           (MAlonzo.Code.Once.Surface.Elaborate.d_elaborate_112
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                              (coe v4) (coe v7))))))
                                               d_functionEpilogue_8) in
                                  coe
                                    (let v12 = d_compileAllFunctions_48 (coe v2) in
                                     coe
                                       (case coe v12 of
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13 -> coe v12
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                            -> coe
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    v11 v13)
                                          _ -> MAlonzo.RTE.mazUnreachableError))
                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_328 v7
                               -> coe
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("Type error in " :: Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (": " :: Data.Text.Text) v7)))
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileX86v3.asmHeader
d_asmHeader_90 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_asmHeader_90
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("# Generated by Once compiler (x86v3 backend)\n"
       ::
       Data.Text.Text)
      (".section .text\n\n" :: Data.Text.Text)
-- Once.CompileX86v3.compileX86v3
d_compileX86v3_92 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileX86v3_92 v0
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
                                                                                   du_go_110
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
                                                                            du_go_110
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
                                                              du_go_110
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
                                                                            du_go_110
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
                                                                     du_go_110
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
                                                       du_go_110
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
                                                           du_go_110
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
                                                    du_go_110
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
                                      du_go_110
                                      (coe
                                         MAlonzo.Code.Once.Parser.d_extractFunctions_58
                                         (coe MAlonzo.Code.Once.Parser.d_extractAliases_18 (coe v6))
                                         (coe v6))))
                         _ -> MAlonzo.RTE.mazUnreachableError)
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.CompileX86v3._.go
d_go_110 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.T_Module_42 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_38] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_110 ~v0 ~v1 v2 = du_go_110 v2
du_go_110 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_38] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_110 v0
  = let v1 = d_compileAllFunctions_48 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 d_asmHeader_90 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
