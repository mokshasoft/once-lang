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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Grammar
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
-- Once.Verified.Compile.gmoduleToModule
d_gmoduleToModule_8
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.gmoduleToModule"
-- Once.Verified.Compile.string-to-bytes
d_string'45'to'45'bytes_10
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.string-to-bytes"
-- Once.Verified.Compile.compile
d_compile_12 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_12 v0 v1
  = let v2 = coe d_gmoduleToModule_8 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> let v4 = coe MAlonzo.Code.Once.CCC.IR.C_Heap_262 in
              coe
                (let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                 coe
                   (let v6 = d_toLegacyArch_6 (coe v0) in
                    coe
                      (let v7
                             = coe
                                 MAlonzo.Code.Once.Parser.du_go_188
                                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v3))
                                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v3))
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                       coe
                         (case coe v7 of
                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                              -> case coe v8 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                     -> let v11
                                              = MAlonzo.Code.Once.Compile.d_compileAllFuns_218
                                                  (coe v4) (coe v5) (coe v9)
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_212
                                                     (coe v10)) in
                                        coe
                                          (case coe v11 of
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                               -> let v13
                                                        = coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            (MAlonzo.Code.Once.Target.d_asmHeader_36
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_archTarget_386
                                                                  (coe v6)))
                                                            (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_420
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_archTarget_386
                                                                  (coe v6))
                                                               (coe v12)) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                       (coe d_string'45'to'45'bytes_10 v13))
                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.compile-asm
d_compile'45'asm_50 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_454
d_compile'45'asm_50 v0 v1
  = let v2 = coe d_gmoduleToModule_8 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_556
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
                (coe MAlonzo.Code.Once.Compile.C_Build_452)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe d_toLegacyArch_6 (coe v0)) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Compile.C_Error_462
                (coe ("GModule \8594 Module conversion failed" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.compile-cli-asm
d_compile'45'cli'45'asm_70 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Compile.T_Stage_446 ->
  Bool ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_454
d_compile'45'cli'45'asm_70 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_556 (coe v0) (coe v1)
      (coe v2) (coe d_toLegacyArch_6 (coe v3)) (coe v4)
-- Once.Verified.Compile.⟦_⟧M
d_'10214'_'10215'M_82
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.\10214_\10215M"
-- Once.Verified.Compile.⟦_⟧A_
d_'10214'_'10215'A__84
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.\10214_\10215A_"
-- Once.Verified.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_90
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.gmoduleToModule-correct"
-- Once.Verified.Compile.module-to-asm-correct
d_module'45'to'45'asm'45'correct_98
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.module-to-asm-correct"
-- Once.Verified.Compile.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_104
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.string-to-bytes-correct"
-- Once.Verified.Compile.correct
d_correct_112 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_112 = erased
