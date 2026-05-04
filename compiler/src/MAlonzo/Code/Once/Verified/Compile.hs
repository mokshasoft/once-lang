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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Verified.CPU.Interface

-- Once.Verified.Compile.toLegacyArch
d_toLegacyArch_6 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Compile.T_Arch_316
d_toLegacyArch_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Verified.CPU.Interface.C_x86'45'64_12
        -> coe MAlonzo.Code.Once.Compile.C_x86'45'64_318
      MAlonzo.Code.Once.Verified.CPU.Interface.C_x86'45'32_14
        -> coe MAlonzo.Code.Once.Compile.C_x86'45'32_320
      MAlonzo.Code.Once.Verified.CPU.Interface.C_riscv64_16
        -> coe MAlonzo.Code.Once.Compile.C_riscv64_322
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
           -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
              coe
                (let v5 = d_toLegacyArch_6 (coe v0) in
                 coe
                   (let v6
                          = coe
                              MAlonzo.Code.Once.Parser.du_go_188
                              (coe MAlonzo.Code.Once.Parser.d_extractAliases_64 (coe v3))
                              (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v3))
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                    coe
                      (case coe v6 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                           -> case coe v7 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                  -> let v10
                                           = MAlonzo.Code.Once.Compile.d_compileAllFuns_182
                                               (coe v4) (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_buildPolyCtx_176
                                                  (coe v9)) in
                                     coe
                                       (case coe v10 of
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                            -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                            -> let v12
                                                     = coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         (MAlonzo.Code.Once.Target.d_asmHeader_36
                                                            (coe
                                                               MAlonzo.Code.Once.Compile.d_archTarget_324
                                                               (coe v5)))
                                                         (coe
                                                            MAlonzo.Code.Once.Compile.d_compileAllWithTarget_344
                                                            (MAlonzo.Code.Once.Compile.d_archTarget_324
                                                               (coe v5))
                                                            v11) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                    (coe d_string'45'to'45'bytes_10 v12))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         _ -> MAlonzo.RTE.mazUnreachableError)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.compile-asm
d_compile'45'asm_50 ::
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_360
d_compile'45'asm_50 v0 v1
  = let v2 = coe d_gmoduleToModule_8 v1 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_456
                (coe MAlonzo.Code.Once.Compile.C_Build_358)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe d_toLegacyArch_6 (coe v0)) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Compile.C_Error_368
                (coe ("GModule \8594 Module conversion failed" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.compile-cli-asm
d_compile'45'cli'45'asm_70 ::
  MAlonzo.Code.Once.Compile.T_Stage_352 ->
  Bool ->
  MAlonzo.Code.Once.Verified.CPU.Interface.T_Arch_10 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_360
d_compile'45'cli'45'asm_70 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_456 (coe v0) (coe v1)
      (coe d_toLegacyArch_6 (coe v2)) (coe v3)
-- Once.Verified.Compile.correct
d_correct_86
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.Compile.correct"
