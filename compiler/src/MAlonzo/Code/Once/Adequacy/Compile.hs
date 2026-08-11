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

module MAlonzo.Code.Once.Adequacy.Compile where

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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CanonModule
import qualified MAlonzo.Code.Once.Adequacy.CanonReflectModule
import qualified MAlonzo.Code.Once.Adequacy.CanonResolve
import qualified MAlonzo.Code.Once.Adequacy.FrontEndBridge
import qualified MAlonzo.Code.Once.Adequacy.MainBuilds
import qualified MAlonzo.Code.Once.Adequacy.MainExtract
import qualified MAlonzo.Code.Once.Adequacy.ModuleComplete
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.MainMeaning
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786
d_compile'45'asm_6 v0 v1
  = let v2
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_68
              (coe
                 MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14 (coe v1))
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_64
                 (coe
                    MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_306
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16 (coe v1))))
                             (coe
                                MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v1)))))
                             (\ v2 v3 v4 ->
                                coe
                                  MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                  (coe
                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                           (coe v1))))))))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Parser.Module.d_r_368
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                      (coe v1)))))))
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
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v1))))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                            (coe v1)))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                              (coe v1))))))))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_982
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_784)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Compile.C_Error_794
                (coe
                   ("front-end (parse / import resolution) failed" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.compile-cli-asm
d_compile'45'cli'45'asm_26 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Compile.T_Stage_778 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786
d_compile'45'cli'45'asm_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_982 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.⟦_⟧M
d_'10214'_'10215'M_38 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'M_38 v0
  = coe
      MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_56
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v0))
-- Once.Adequacy.Compile.ArchCorrect
d_ArchCorrect_46 a0 a1 = ()
data T_ArchCorrect_46
  = C_constructor_104 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
                      (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
                       Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
-- Once.Adequacy.Compile.ArchCorrect.asm-sem
d_asm'45'sem_78 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_asm'45'sem_78 v0
  = case coe v0 of
      C_constructor_104 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.flat-trace
d_flat'45'trace_80 ::
  T_ArchCorrect_46 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'trace_80 v0
  = case coe v0 of
      C_constructor_104 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.assemble-correct
d_assemble'45'correct_88 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assemble'45'correct_88 = erased
-- Once.Adequacy.Compile.ArchCorrect.asm-trace-correct
d_asm'45'trace'45'correct_96 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct_96 = erased
-- Once.Adequacy.Compile.ArchCorrect.ir-flat-correct
d_ir'45'flat'45'correct_102 ::
  T_ArchCorrect_46 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct_102 = erased
-- Once.Adequacy.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_112 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gmoduleToModule'45'correct_112 = erased
-- Once.Adequacy.Compile.WithCPU.exec
d_exec_130 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_exec_130 v0 ~v1 v2 v3 = du_exec_130 v0 v2 v3
du_exec_130 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_exec_130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0 v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU.string-to-bytes
d_string'45'to'45'bytes_136 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_136 v0 ~v1 v2
  = du_string'45'to'45'bytes_136 v0 v2
du_string'45'to'45'bytes_136 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_string'45'to'45'bytes_136 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 (coe v0 v1)
-- Once.Adequacy.Compile.WithCPU.compile-cr
d_compile'45'cr_140 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_140 v0 ~v1 v2 v3 = du_compile'45'cr_140 v0 v2 v3
du_compile'45'cr_140 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'cr_140 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Compile.C_Parsed_788 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Checked_790 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Built_792 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_string'45'to'45'bytes_136 v0 v1 v3)
      MAlonzo.Code.Once.Compile.C_Error_794 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-mir
d_compile'45'mir_152 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_152 v0 ~v1 v2 v3 v4 v5
  = du_compile'45'mir_152 v0 v2 v3 v4 v5
du_compile'45'mir_152 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_152 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_compile'45'cr_140 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_982
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_784) (coe v2) (coe v1)
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-gm
d_compile'45'gm_166 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_166 v0 ~v1 v2 v3 v4
  = du_compile'45'gm_166 v0 v2 v3 v4
du_compile'45'gm_166 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_166 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_compile'45'mir_152 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile
d_compile_178 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_178 v0 ~v1 v2 v3 v4 = du_compile_178 v0 v2 v3 v4
du_compile_178 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_178 v0 v1 v2 v3
  = coe
      du_compile'45'gm_166 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_76 (coe v3))
-- Once.Adequacy.Compile.WithCPU.⟦_⟧A_
d_'10214'_'10215'A__186 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'A__186 ~v0 v1 v2 v3
  = du_'10214'_'10215'A__186 v1 v2 v3
du_'10214'_'10215'A__186 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_'10214'_'10215'A__186 v0 v1 v2
  = coe d_asm'45'sem_78 (coe v0 v1) v2
-- Once.Adequacy.Compile.WithCPU.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_200 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_200 = erased
-- Once.Adequacy.Compile.WithCPU.codegen-asm-correct
d_codegen'45'asm'45'correct_220 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_220 = erased
-- Once.Adequacy.Compile.WithCPU.module-to-asm-correct
d_module'45'to'45'asm'45'correct_240 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_240 = erased
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_252 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'ir_252 ~v0 ~v1 v2
  = du_'10214'_'10215''8869''45'ir_252 v2
du_'10214'_'10215''8869''45'ir_252 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869''45'ir_252 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_56
                (coe v0))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_256 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'm_256 ~v0 ~v1 v2
  = du_'10214'_'10215''8869''45'm_256 v2
du_'10214'_'10215''8869''45'm_256 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869''45'm_256 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             du_'10214'_'10215''8869''45'ir_252
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥
d_'10214'_'10215''8869'_260 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869'_260 ~v0 ~v1 v2
  = du_'10214'_'10215''8869'_260 v2
du_'10214'_'10215''8869'_260 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869'_260 v0
  = coe
      du_'10214'_'10215''8869''45'm_256
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_76 (coe v0))
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_270 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_270 ~v0 ~v1 v2 ~v3 ~v4
  = du_'10214''10215''8869''45'ir'45'sound_270 v2
du_'10214''10215''8869''45'ir'45'sound_270 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'ir'45'sound_270 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_286 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_286 ~v0 ~v1 v2 ~v3 ~v4
  = du_'10214''10215''8869''45'm'45'sound_286 v2
du_'10214''10215''8869''45'm'45'sound_286 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'm'45'sound_286 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_598
                   (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_302 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_302 ~v0 ~v1 v2 ~v3 ~v4
  = du_'10214''10215''8869''45'sound_302 v2
du_'10214''10215''8869''45'sound_302 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'sound_302 v0
  = coe
      du_'10214''10215''8869''45'm'45'sound_286
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_76 (coe v0))
-- Once.Adequacy.Compile.WithCPU.opt-trace
d_opt'45'trace_320
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.Compile.WithCPU.opt-trace"
-- Once.Adequacy.Compile.WithCPU._≋_
d__'8779'__322 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d__'8779'__322 = erased
-- Once.Adequacy.Compile.WithCPU.TraceAt
d_TraceAt_330 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_330 = erased
-- Once.Adequacy.Compile.WithCPU.correct-cr
d_correct'45'cr_352 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 v9
  = du_correct'45'cr_352 v6 v7 v9
du_correct'45'cr_352 ::
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'cr_352 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Compile.C_Parsed_788 v3 v4 -> erased
      MAlonzo.Code.Once.Compile.C_Checked_790 v3 -> erased
      MAlonzo.Code.Once.Compile.C_Built_792 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_just_40
             (coe v2 v3 v1)
      MAlonzo.Code.Once.Compile.C_Error_794 v3 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct-mir
d_correct'45'mir_422 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_422 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_correct'45'mir_422 v2 v3 v4 v5
du_correct'45'mir_422 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'mir_422 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_correct'45'cr_352
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_982
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_784) (coe v1) (coe v0)
                (coe v2))
             erased erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct-gm
d_correct'45'gm_456 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm_456 ~v0 ~v1 v2 v3 v4 ~v5
  = du_correct'45'gm_456 v2 v3 v4
du_correct'45'gm_456 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm_456 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_correct'45'mir_422 (coe v0) (coe v1) (coe v3)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct
d_correct_482 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_482 ~v0 ~v1 v2 v3 v4 = du_correct_482 v2 v3 v4
du_correct_482 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_482 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         du_correct'45'gm_456 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_76 (coe v2)))
-- Once.Adequacy.Compile.WithCPU.pw-just-inv
d_pw'45'just'45'inv_528 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_528 ~v0 ~v1 ~v2 v3 ~v4
  = du_pw'45'just'45'inv_528 v3
du_pw'45'just'45'inv_528 ::
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pw'45'just'45'inv_528 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-sound
d_accept'45'sound_542 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'sound_542 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_accept'45'sound_542 v4
du_accept'45'sound_542 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'sound_542 v0
  = coe du_'10214''10215''8869''45'sound_302 (coe v0)
-- Once.Adequacy.Compile.WithCPU.Typed
d_Typed_562 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) -> ()
d_Typed_562 = erased
-- Once.Adequacy.Compile.WithCPU._⊢R_
d__'8866'R__568 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d__'8866'R__568 = erased
-- Once.Adequacy.Compile.WithCPU.main-realize-agrees
d_main'45'realize'45'agrees_586 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'realize'45'agrees_586 = erased
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ˢ
d_'10214'_'10215''738'_588 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215''738'_588 ~v0 ~v1 v2
  = du_'10214'_'10215''738'_588 v2
du_'10214'_'10215''738'_588 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_'10214'_'10215''738'_588 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Once.Adequacy.MainExtract.du_runMain'738'_10
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Adequacy.ModuleComplete.d_mainRealized_674
                          (coe v1) (coe v3) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.sd-bridge
d_sd'45'bridge_598 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'bridge_598 = erased
-- Once.Adequacy.Compile.WithCPU.pw-just-rel
d_pw'45'just'45'rel_614 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45'just'45'rel_614 = erased
-- Once.Adequacy.Compile.WithCPU.compile-just-ir
d_compile'45'just'45'ir_630 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_compile'45'just'45'ir_630 v5
du_compile'45'just'45'ir_630 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'just'45'ir_630 v0
  = let v1
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR'45'aux_48
              (coe
                 MAlonzo.Code.Once.Compile.d_compileResolvedModule'45'aux_554
                 (coe MAlonzo.Code.Once.IR.C_Heap_8)
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0)
                 (coe
                    MAlonzo.Code.Once.Parser.d_guardDistinct_526
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.WithCPU._.c≡n
d_c'8801'n_686 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_686 = erased
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-just
d_'10214''10215''8869''45'just_702 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_702 = erased
-- Once.Adequacy.Compile.WithCPU.correctR-sound
d_correctR'45'sound_732 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'sound_732 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_correctR'45'sound_732 v4
du_correctR'45'sound_732 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'sound_732 v0
  = let v1
          = coe
              du_'10214''10215''8869''45'm'45'sound_286
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_68
                 (coe
                    MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14 (coe v0))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_64
                    (coe
                       MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_306
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v0))))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                            (coe v0)))))
                                (\ v1 v2 v3 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                              (coe v0))))))))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Parser.Module.d_r_368
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v0)))))))
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
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                            (coe v0))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                      (coe
                                         MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                            (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                               (coe v0)))))
                                   (\ v1 v2 v3 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                        (coe
                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                 (coe v0)))))))))))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> let v6
                           = MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR'45'aux_48
                               (coe
                                  MAlonzo.Code.Once.Compile.d_compileResolvedModule'45'aux_554
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2)
                                  (coe
                                     MAlonzo.Code.Once.Parser.d_guardDistinct_526
                                     (coe
                                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v2))
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v2))
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> let v8
                                     = coe
                                         MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_128
                                         (coe
                                            MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_306
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                              (coe v0))))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                 (coe v0)))))
                                                     (\ v8 v9 v10 ->
                                                        coe
                                                          MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                   (coe v0))))))))
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.d_r_368
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                              (coe v0)))))))
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
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                 (coe v0))))
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                 (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                    (coe v0)))))
                                                        (\ v8 v9 v10 ->
                                                           coe
                                                             MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                      (coe v0)))))))))) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> coe
                                           seq (coe v10)
                                           (let v11
                                                  = coe
                                                      MAlonzo.Code.Once.Adequacy.CanonReflectModule.du_go_144
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14
                                                         (coe v0))
                                                      (coe v9) (coe v2) (coe v5)
                                                      (coe
                                                         MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_926
                                                         (coe v2) (coe v5) (coe v7))
                                                      (coe
                                                         MAlonzo.Code.Once.Adequacy.CanonResolve.d_noImports'63'_16
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                            (coe v9))) in
                                            coe
                                              (coe
                                                 seq (coe v11)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v9) (coe v11))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_496
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                             (coe v0)))
                                                       erased))))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> let v7 = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12 in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> let v10
                                               = coe
                                                   MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_128
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_306
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                        (coe v0))))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                           (coe v0)))))
                                                               (\ v10 v11 v12 ->
                                                                  coe
                                                                    MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                          (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                             (coe v0))))))))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.d_r_368
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                        (coe v0)))))))
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
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                           (coe v0))))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                              (coe v0)))))
                                                                  (\ v10 v11 v12 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_560
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                             (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                                (coe v0)))))))))) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                -> coe
                                                     seq (coe v12)
                                                     (let v13
                                                            = coe
                                                                MAlonzo.Code.Once.Adequacy.CanonReflectModule.du_go_144
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14
                                                                   (coe v0))
                                                                (coe v11) (coe v2) (coe v5)
                                                                (coe
                                                                   MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_926
                                                                   (coe v2) (coe v5) (coe v8))
                                                                (coe
                                                                   MAlonzo.Code.Once.Adequacy.CanonResolve.d_noImports'63'_16
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                                      (coe v11))) in
                                                      coe
                                                        (coe
                                                           seq (coe v13)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v11) (coe v13))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_496
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                       (coe v0)))
                                                                 erased))))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.WithCPU.correctR-complete
d_correctR'45'complete_878 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_878 v0 ~v1 v2 v3 v4 v5 ~v6
  = du_correctR'45'complete_878 v0 v2 v3 v4 v5
du_correctR'45'complete_878 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'complete_878 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> let v9
                        = MAlonzo.Code.Once.Adequacy.CanonModule.d_go_50
                            (coe
                               MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14 (coe v3))
                            (coe v5) (coe v7) (coe v8)
                            (coe
                               MAlonzo.Code.Once.Adequacy.CanonResolve.d_noImports'63'_16
                               (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v5))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> case coe v11 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                -> case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                       -> let v16
                                                = let v16
                                                        = MAlonzo.Code.Once.Parser.d_guardDistinct_526
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                                  (coe v10))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                                  (coe v10))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
                                                  coe
                                                    (let v17
                                                           = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe v15) in
                                                     coe
                                                       (let v18
                                                              = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                  (coe v15) in
                                                        coe
                                                          (case coe v16 of
                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                                                               -> case coe v19 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                      -> let v22
                                                                               = MAlonzo.Code.Once.Adequacy.ModuleComplete.d_caf'45'go'45'find'45'complete_286
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Compile.d_buildPolyCtx_270
                                                                                      (coe v21))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                                                         (coe v10)))
                                                                                   (coe v20)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)
                                                                                   (coe v14)
                                                                                   (coe v17)
                                                                                   (coe v18) in
                                                                         coe
                                                                           (case coe v22 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                -> case coe v24 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                                                       -> coe
                                                                                            seq
                                                                                            (coe
                                                                                               v26)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v25)
                                                                                               erased)
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError))) in
                                          coe
                                            (coe
                                               seq (coe v16)
                                               (let v17
                                                      = coe
                                                          MAlonzo.Code.Once.Adequacy.MainBuilds.du_cfm'45'built'45'aux_542
                                                          (coe v1)
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.d_guardDistinct_526
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                                   (coe v10))
                                                                (coe
                                                                   MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                                   (coe v10))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                MAlonzo.Code.Once.Adequacy.MainBuilds.du_crm'45'doOpt_522
                                                                (coe v2) (coe v10))) in
                                                coe
                                                  (case coe v17 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               du_string'45'to'45'bytes_136 v0 v1
                                                               v18)
                                                            erased
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.p-eq
d_p'45'eq_988 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'45'eq_988 = erased
-- Once.Adequacy.Compile.WithCPU._.stm-eq
d_stm'45'eq_990 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stm'45'eq_990 = erased
-- Once.Adequacy.Compile.WithCPU._.c≡j
d_c'8801'j_992 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'j_992 = erased
-- Once.Adequacy.Compile.WithCPU.correctR
d_correctR_1020 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR_1020 v0 ~v1 v2 v3 v4 = du_correctR_1020 v0 v2 v3 v4
du_correctR_1020 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR_1020 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v4 v5 -> coe du_correctR'45'sound_732 (coe v3))
      (\ v4 v5 ->
         coe
           du_correctR'45'complete_878 (coe v0) (coe v1) (coe v2) (coe v3) v4)
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ᵈ
d_'10214'_'10215''7496'_1036 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215''7496'_1036 ~v0 ~v1 v2
  = du_'10214'_'10215''7496'_1036 v2
du_'10214'_'10215''7496'_1036 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_'10214'_'10215''7496'_1036 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Once.Denotation.MainMeaning.d_meaning'7496'_144
                    (coe v1) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.bridgeᵈ
d_bridge'7496'_1048 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'7496'_1048 = erased
-- Once.Adequacy.Compile.WithCPU.correctᵈ
d_correct'7496'_1072 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_1072 v0 ~v1 v2 v3 v4
  = du_correct'7496'_1072 v0 v2 v3 v4
du_correct'7496'_1072 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correct'7496'_1072 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v4 v5 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe du_correctR'45'sound_732 (coe v3)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_correctR'45'sound_732 (coe v3))))
                 erased)))
      (\ v4 v5 ->
         coe
           du_correctR'45'complete_878 (coe v0) (coe v1) (coe v2) (coe v3) v4)
