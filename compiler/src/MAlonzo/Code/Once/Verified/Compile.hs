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

module MAlonzo.Code.Once.Verified.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ModuleConvert
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.Compile.toLegacyArch
d_toLegacyArch_6 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Compile.T_Arch_378
d_toLegacyArch_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Verified.CPU.Interface.C_x86'45'64_12
        -> coe MAlonzo.Code.Once.Compile.C_x86'45'64_380
      MAlonzo.Code.Once.Verified.CPU.Interface.C_x86'45'32_14
        -> coe MAlonzo.Code.Once.Compile.C_x86'45'32_382
      MAlonzo.Code.Once.Verified.CPU.Interface.C_riscv64_16
        -> coe MAlonzo.Code.Once.Compile.C_riscv64_384
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.Compile.compile-asm
d_compile'45'asm_8 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_464
d_compile'45'asm_8 v0 v1
  = let v2
          = MAlonzo.Code.Once.Grammar.ModuleConvert.d_mapDecls_122
              (coe MAlonzo.Code.Once.Grammar.d_decls_142 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> let v4
                    = coe
                        MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v3) in
              coe
                (coe
                   MAlonzo.Code.Once.Compile.d_compileFromModule_566
                   (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
                   (coe MAlonzo.Code.Once.Compile.C_Build_462)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe d_toLegacyArch_6 (coe v0)) (coe v4))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Once.Compile.d_compileFromModule_566
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
                       (coe MAlonzo.Code.Once.Compile.C_Build_462)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe d_toLegacyArch_6 (coe v0)) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Once.Compile.C_Error_472
                       (coe ("GModule \8594 Module conversion failed" :: Data.Text.Text))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.compile-cli-asm
d_compile'45'cli'45'asm_28 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Compile.T_Stage_456 ->
  Bool ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_464
d_compile'45'cli'45'asm_28 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_566 (coe v0) (coe v1)
      (coe v2) (coe d_toLegacyArch_6 (coe v3)) (coe v4)
-- Once.Verified.Compile.⟦_⟧M
d_'10214'_'10215'M_40
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.\10214_\10215M"
-- Once.Verified.Compile.⟦_⟧A_
d_'10214'_'10215'A__42
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.\10214_\10215A_"
-- Once.Verified.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_48
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.gmoduleToModule-correct"
-- Once.Verified.Compile.module-to-asm-correct
d_module'45'to'45'asm'45'correct_56
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.module-to-asm-correct"
-- Once.Verified.Compile.WithCPU.exec
d_exec_62 ::
  (MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18) ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] -> Maybe Integer
d_exec_62 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.d_exec'45'bytes_48
      (coe v0 v1) (coe v2)
-- Once.Verified.Compile.WithCPU.string-to-bytes
d_string'45'to'45'bytes_68 ::
  (MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18) ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_68 v0 v1
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.d_assemble_46 (coe v0 v1)
-- Once.Verified.Compile.WithCPU.compile
d_compile_72 ::
  (MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18) ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_72 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Grammar.ModuleConvert.d_mapDecls_122
              (coe MAlonzo.Code.Once.Grammar.d_decls_142 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> let v5
                    = coe
                        MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v4) in
              coe
                (let v6 = coe MAlonzo.Code.Once.CCC.IR.C_Heap_262 in
                 coe
                   (let v7 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                    coe
                      (let v8 = d_toLegacyArch_6 (coe v1) in
                       coe
                         (let v9
                                = coe
                                    MAlonzo.Code.Once.Parser.du_go_188
                                    (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v5))
                                    (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v5))
                                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                          coe
                            (case coe v9 of
                               MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                 -> case coe v10 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                        -> let v13
                                                 = MAlonzo.Code.Once.Compile.d_compileAllFuns_218
                                                     (coe v6) (coe v7) (coe v11)
                                                     (coe
                                                        MAlonzo.Code.Once.Compile.d_buildPolyCtx_212
                                                        (coe v12)) in
                                           coe
                                             (case coe v13 of
                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                                  -> let v15
                                                           = coe
                                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                               (MAlonzo.Code.Once.Target.d_asmHeader_38
                                                                  (coe
                                                                     MAlonzo.Code.Once.Compile.d_archTarget_386
                                                                     (coe v8)))
                                                               (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_424
                                                                  (coe
                                                                     MAlonzo.Code.Once.Compile.d_archTarget_386
                                                                     (coe v8))
                                                                  (coe v14)) in
                                                     coe
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                          (coe
                                                             d_string'45'to'45'bytes_68 v0 v1 v15))
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)))))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> let v5 = coe MAlonzo.Code.Once.CCC.IR.C_Heap_262 in
                     coe
                       (let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                        coe
                          (let v7 = d_toLegacyArch_6 (coe v1) in
                           coe
                             (let v8
                                    = coe
                                        MAlonzo.Code.Once.Parser.du_go_188
                                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v4))
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v4))
                                        (coe v3) in
                              coe
                                (case coe v8 of
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v3
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                                     -> case coe v9 of
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                            -> let v12
                                                     = MAlonzo.Code.Once.Compile.d_compileAllFuns_218
                                                         (coe v5) (coe v6) (coe v10)
                                                         (coe
                                                            MAlonzo.Code.Once.Compile.d_buildPolyCtx_212
                                                            (coe v11)) in
                                               coe
                                                 (case coe v12 of
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                                      -> coe v3
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                                      -> let v14
                                                               = coe
                                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                   (MAlonzo.Code.Once.Target.d_asmHeader_38
                                                                      (coe
                                                                         MAlonzo.Code.Once.Compile.d_archTarget_386
                                                                         (coe v7)))
                                                                   (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_424
                                                                      (coe
                                                                         MAlonzo.Code.Once.Compile.d_archTarget_386
                                                                         (coe v7))
                                                                      (coe v13)) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe
                                                                 d_string'45'to'45'bytes_68 v0 v1
                                                                 v14))
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                   _ -> MAlonzo.RTE.mazUnreachableError))))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.WithCPU.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_114
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.WithCPU.string-to-bytes-correct"
-- Once.Verified.Compile.WithCPU.correct
d_correct_122 ::
  (MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_18) ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_122 = erased
