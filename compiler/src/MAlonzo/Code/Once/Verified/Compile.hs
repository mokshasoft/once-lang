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
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Verified.CPU.Interface
import qualified MAlonzo.Code.Once.Verified.SourceTrace
import qualified MAlonzo.Code.Once.Verified.Trace

-- Once.Verified.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_586
d_compile'45'asm_6 v0 v1
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
                   MAlonzo.Code.Once.Compile.d_compileFromModule_698
                   (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
                   (coe MAlonzo.Code.Once.Compile.C_Build_584)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v4))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Once.Compile.d_compileFromModule_698
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
                       (coe MAlonzo.Code.Once.Compile.C_Build_584)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Once.Compile.C_Error_594
                       (coe ("GModule \8594 Module conversion failed" :: Data.Text.Text))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.compile-cli-asm
d_compile'45'cli'45'asm_26 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Compile.T_Stage_578 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_586
d_compile'45'cli'45'asm_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_698 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4)
-- Once.Verified.Compile.⟦_⟧M
d_'10214'_'10215'M_38 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_'10214'_'10215'M_38 v0
  = coe
      MAlonzo.Code.Once.Verified.SourceTrace.d_'10214'_'10215'IR_44
      (coe
         MAlonzo.Code.Once.Verified.SourceTrace.d_moduleToIR_40 (coe v0))
-- Once.Verified.Compile.ArchCorrect
d_ArchCorrect_46 a0 a1 = ()
data T_ArchCorrect_46
  = C_constructor_100 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136])
                      (Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
                       Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136])
-- Once.Verified.Compile.ArchCorrect.asm-sem
d_asm'45'sem_76 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_asm'45'sem_76 v0
  = case coe v0 of
      C_constructor_100 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.Compile.ArchCorrect.flat-trace
d_flat'45'trace_78 ::
  T_ArchCorrect_46 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_flat'45'trace_78 v0
  = case coe v0 of
      C_constructor_100 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.Compile.ArchCorrect.assemble-correct
d_assemble'45'correct_84 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assemble'45'correct_84 = erased
-- Once.Verified.Compile.ArchCorrect.asm-trace-correct
d_asm'45'trace'45'correct_92 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct_92 = erased
-- Once.Verified.Compile.ArchCorrect.ir-flat-correct
d_ir'45'flat'45'correct_98 ::
  T_ArchCorrect_46 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct_98 = erased
-- Once.Verified.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_108 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gmoduleToModule'45'correct_108 = erased
-- Once.Verified.Compile.WithCPU.exec
d_exec_126 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_exec_126 v0 ~v1 v2 v3 = du_exec_126 v0 v2 v3
du_exec_126 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
du_exec_126 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.d_exec'45'bytes_40
      (coe v0 v1) (coe v2)
-- Once.Verified.Compile.WithCPU.string-to-bytes
d_string'45'to'45'bytes_132 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_132 v0 ~v1 v2
  = du_string'45'to'45'bytes_132 v0 v2
du_string'45'to'45'bytes_132 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_string'45'to'45'bytes_132 v0 v1
  = coe
      MAlonzo.Code.Once.Verified.CPU.Interface.d_assemble_38 (coe v0 v1)
-- Once.Verified.Compile.WithCPU.compile
d_compile_136 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_136 v0 ~v1 v2 v3 = du_compile_136 v0 v2 v3
du_compile_136 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_136 v0 v1 v2
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
                      (let v8
                             = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v5))
                                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v5))
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                       coe
                         (case coe v8 of
                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                              -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                              -> case coe v9 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                     -> let v12
                                              = MAlonzo.Code.Once.Compile.d_compileAllFuns_410
                                                  (coe v6) (coe v7) (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_226
                                                     (coe v11)) in
                                        coe
                                          (case coe v12 of
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                               -> let v14
                                                        = coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            (MAlonzo.Code.Once.Target.d_asmHeader_38
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_archTarget_508
                                                                  (coe v1)))
                                                            (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_546
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_archTarget_508
                                                                  (coe v1))
                                                               (coe v13)) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                       (coe du_string'45'to'45'bytes_132 v0 v1 v14))
                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError))))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> let v5 = coe MAlonzo.Code.Once.CCC.IR.C_Heap_262 in
                     coe
                       (let v6 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                        coe
                          (let v7
                                 = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                                     (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v4))
                                     (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v4))
                                     (coe v3) in
                           coe
                             (case coe v7 of
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v3
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                                  -> case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                         -> let v11
                                                  = MAlonzo.Code.Once.Compile.d_compileAllFuns_410
                                                      (coe v5) (coe v6) (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Once.Compile.d_buildPolyCtx_226
                                                         (coe v10)) in
                                            coe
                                              (case coe v11 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                                   -> coe v3
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                                   -> let v13
                                                            = coe
                                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                (MAlonzo.Code.Once.Target.d_asmHeader_38
                                                                   (coe
                                                                      MAlonzo.Code.Once.Compile.d_archTarget_508
                                                                      (coe v1)))
                                                                (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_546
                                                                   (coe
                                                                      MAlonzo.Code.Once.Compile.d_archTarget_508
                                                                      (coe v1))
                                                                   (coe v12)) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                           (coe
                                                              du_string'45'to'45'bytes_132 v0 v1
                                                              v13))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.Compile.WithCPU.⟦_⟧A_
d_'10214'_'10215'A__174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_'10214'_'10215'A__174 ~v0 v1 v2 v3
  = du_'10214'_'10215'A__174 v1 v2 v3
du_'10214'_'10215'A__174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
du_'10214'_'10215'A__174 v0 v1 v2
  = coe d_asm'45'sem_76 (coe v0 v1) v2
-- Once.Verified.Compile.WithCPU.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_186 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_186 = erased
-- Once.Verified.Compile.WithCPU.codegen-asm-correct
d_codegen'45'asm'45'correct_202 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_202 = erased
-- Once.Verified.Compile.WithCPU.module-to-asm-correct
d_module'45'to'45'asm'45'correct_222 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_222 = erased
-- Once.Verified.Compile.WithCPU.correct
d_correct_242 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Verified.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_correct_242 = erased
