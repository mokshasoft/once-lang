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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
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
import qualified MAlonzo.Code.Once.Denotation.Admissible
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
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786
d_compile'45'asm_6 v0 v1
  = let v2
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_70
              (coe
                 MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14 (coe v1))
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_66
                 (coe
                    MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16 (coe v1))))
                             (coe
                                MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v1)))))
                             (\ v2 v3 v4 ->
                                coe
                                  MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                  (coe
                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                           (coe v1))))))))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Parser.Module.d_r_370
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
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
                                MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v1))))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                            (coe v1)))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                              (coe v1))))))))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1092
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
      MAlonzo.Code.Once.Compile.d_compileFromModule_1092 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.⟦_⟧M
d_'10214'_'10215'M_38 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_'10214'_'10215'M_38 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_56
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v1))
-- Once.Adequacy.Compile.ArchCorrect
d_ArchCorrect_48 a0 a1 = ()
data T_ArchCorrect_48
  = C_constructor_106 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
                      (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
                       Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
-- Once.Adequacy.Compile.ArchCorrect.asm-sem
d_asm'45'sem_80 ::
  T_ArchCorrect_48 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_asm'45'sem_80 v0
  = case coe v0 of
      C_constructor_106 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.flat-trace
d_flat'45'trace_82 ::
  T_ArchCorrect_48 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_flat'45'trace_82 v0
  = case coe v0 of
      C_constructor_106 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.assemble-correct
d_assemble'45'correct_90 ::
  T_ArchCorrect_48 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assemble'45'correct_90 = erased
-- Once.Adequacy.Compile.ArchCorrect.asm-trace-correct
d_asm'45'trace'45'correct_98 ::
  T_ArchCorrect_48 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct_98 = erased
-- Once.Adequacy.Compile.ArchCorrect.ir-flat-correct
d_ir'45'flat'45'correct_104 ::
  T_ArchCorrect_48 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct_104 = erased
-- Once.Adequacy.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_116 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gmoduleToModule'45'correct_116 = erased
-- Once.Adequacy.Compile.WithCPU.exec
d_exec_138 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_exec_138 v0 ~v1 v2 v3 = du_exec_138 v0 v2 v3
du_exec_138 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_exec_138 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0 v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU.string-to-bytes
d_string'45'to'45'bytes_144 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_144 v0 ~v1 v2
  = du_string'45'to'45'bytes_144 v0 v2
du_string'45'to'45'bytes_144 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_string'45'to'45'bytes_144 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 (coe v0 v1)
-- Once.Adequacy.Compile.WithCPU.compile-cr
d_compile'45'cr_148 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_148 v0 ~v1 v2 v3 = du_compile'45'cr_148 v0 v2 v3
du_compile'45'cr_148 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'cr_148 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Compile.C_Parsed_788 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Checked_790 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Built_792 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_string'45'to'45'bytes_144 v0 v1 v3)
      MAlonzo.Code.Once.Compile.C_Error_794 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-mir
d_compile'45'mir_160 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_160 v0 ~v1 v2 v3 v4 v5
  = du_compile'45'mir_160 v0 v2 v3 v4 v5
du_compile'45'mir_160 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_160 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_compile'45'cr_148 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1092
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_784) (coe v2) (coe v1)
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-gm
d_compile'45'gm_174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_174 v0 ~v1 v2 v3 v4
  = du_compile'45'gm_174 v0 v2 v3 v4
du_compile'45'gm_174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_174 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_compile'45'mir_160 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile
d_compile_186 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_186 v0 ~v1 v2 v3 v4 = du_compile_186 v0 v2 v3 v4
du_compile_186 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_186 v0 v1 v2 v3
  = coe
      du_compile'45'gm_174 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_78 (coe v3))
-- Once.Adequacy.Compile.WithCPU.⟦_⟧A_
d_'10214'_'10215'A__194 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_'10214'_'10215'A__194 ~v0 v1 v2 v3
  = du_'10214'_'10215'A__194 v1 v2 v3
du_'10214'_'10215'A__194 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_'10214'_'10215'A__194 v0 v1 v2
  = coe d_asm'45'sem_80 (coe v0 v1) v2
-- Once.Adequacy.Compile.WithCPU.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_208 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_208 = erased
-- Once.Adequacy.Compile.WithCPU.codegen-asm-correct
d_codegen'45'asm'45'correct_228 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_228 = erased
-- Once.Adequacy.Compile.WithCPU.module-to-asm-correct
d_module'45'to'45'asm'45'correct_248 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_248 = erased
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_260 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
d_'10214'_'10215''8869''45'ir_260 ~v0 ~v1 v2 v3
  = du_'10214'_'10215''8869''45'ir_260 v2 v3
du_'10214'_'10215''8869''45'ir_260 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
du_'10214'_'10215''8869''45'ir_260 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_56
                (coe v0)
                (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v1)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-adm
d_'10214'_'10215''8869''45'adm_270 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
d_'10214'_'10215''8869''45'adm_270 ~v0 ~v1 v2 v3 v4
  = du_'10214'_'10215''8869''45'adm_270 v2 v3 v4
du_'10214'_'10215''8869''45'adm_270 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
du_'10214'_'10215''8869''45'adm_270 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       du_'10214'_'10215''8869''45'ir_260
                       (coe
                          MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v0))
                       (coe v1))
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_280 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
d_'10214'_'10215''8869''45'm_280 ~v0 ~v1 v2 v3
  = du_'10214'_'10215''8869''45'm_280 v2 v3
du_'10214'_'10215''8869''45'm_280 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
du_'10214'_'10215''8869''45'm_280 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_'10214'_'10215''8869''45'adm_270 (coe v2) (coe v1)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v1) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥
d_'10214'_'10215''8869'_286 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
d_'10214'_'10215''8869'_286 ~v0 ~v1 v2 v3
  = du_'10214'_'10215''8869'_286 v2 v3
du_'10214'_'10215''8869'_286 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118])
du_'10214'_'10215''8869'_286 v0 v1
  = coe
      du_'10214'_'10215''8869''45'm_280
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_78 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_300 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_300 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_'10214''10215''8869''45'ir'45'sound_300 v2
du_'10214''10215''8869''45'ir'45'sound_300 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'ir'45'sound_300 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-adm-sound
d_'10214''10215''8869''45'adm'45'sound_322 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'10214''10215''8869''45'adm'45'sound_322 ~v0 ~v1 v2 ~v3 v4 ~v5
                                           ~v6
  = du_'10214''10215''8869''45'adm'45'sound_322 v2 v4
du_'10214''10215''8869''45'adm'45'sound_322 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_'10214''10215''8869''45'adm'45'sound_322 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_598
                   (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_346 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_346 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'10214''10215''8869''45'm'45'sound_346 v2 v3
du_'10214''10215''8869''45'm'45'sound_346 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'm'45'sound_346 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   du_'10214''10215''8869''45'adm'45'sound_322 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                      (coe v1) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_368 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_368 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'10214''10215''8869''45'sound_368 v2 v3
du_'10214''10215''8869''45'sound_368 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'sound_368 v0 v1
  = coe
      du_'10214''10215''8869''45'm'45'sound_346
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_78 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU.opt-trace
d_opt'45'trace_388
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.Compile.WithCPU.opt-trace"
-- Once.Adequacy.Compile.WithCPU._≋_
d__'8779'__390 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  ()
d__'8779'__390 = erased
-- Once.Adequacy.Compile.WithCPU.TraceAt
d_TraceAt_398 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_398 = erased
-- Once.Adequacy.Compile.WithCPU.correct-cr
d_correct'45'cr_420 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 v10
  = du_correct'45'cr_420 v6 v8 v10
du_correct'45'cr_420 ::
  MAlonzo.Code.Once.Compile.T_CompileResult_786 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'cr_420 v0 v1 v2
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
d_correct'45'mir_498 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_498 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_correct'45'mir_498 v2 v3 v4 v5
du_correct'45'mir_498 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'mir_498 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_correct'45'cr_420
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1092
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_784) (coe v1) (coe v0)
                (coe v2))
             erased erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.refuse-gated
d_refuse'45'gated_538 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gated_538 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-ef
d_refuse'45'ef_574 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'ef_574 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-mir
d_refuse'45'mir_606 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'mir_606 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-gm
d_refuse'45'gm_632 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gm_632 = erased
-- Once.Adequacy.Compile.WithCPU.accept-gated
d_accept'45'gated_656 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gated_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_accept'45'gated_656 v7
du_accept'45'gated_656 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gated_656 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-ef
d_accept'45'ef_692 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'ef_692 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7
  = du_accept'45'ef_692 v2 v4 v5
du_accept'45'ef_692 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'ef_692 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             seq (coe v3)
             (coe
                du_accept'45'gated_656
                (coe
                   MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                   (coe v0) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-mir
d_accept'45'mir_724 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'mir_724 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7
  = du_accept'45'mir_724 v2 v4 v5
du_accept'45'mir_724 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'mir_724 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'ef_692 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Parser.d_extractFunctions_540
            (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
            (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-gm
d_accept'45'gm_750 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gm_750 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6
  = du_accept'45'gm_750 v2 v4
du_accept'45'gm_750 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gm_750 v0 v1
  = coe
      du_accept'45'mir_724 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v1))
-- Once.Adequacy.Compile.WithCPU.correct-gm
d_correct'45'gm_770 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
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
d_correct'45'gm_770 ~v0 ~v1 v2 v3 v4 ~v5
  = du_correct'45'gm_770 v2 v3 v4
du_correct'45'gm_770 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm_770 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_correct'45'gm'45'adm_782 (coe v0) (coe v1) (coe v3)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v0) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct-gm-adm
d_correct'45'gm'45'adm_782 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm'45'adm_782 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_correct'45'gm'45'adm_782 v2 v3 v4 v5
du_correct'45'gm'45'adm_782 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm'45'adm_782 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_correct'45'mir_498 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_52 (coe v2)))
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct
d_correct_836 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_836 ~v0 ~v1 v2 v3 v4 = du_correct_836 v2 v3 v4
du_correct_836 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_836 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         du_correct'45'gm_770 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_78 (coe v2)))
-- Once.Adequacy.Compile.WithCPU.pw-just-inv
d_pw'45'just'45'inv_882 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_882 ~v0 ~v1 ~v2 v3 ~v4
  = du_pw'45'just'45'inv_882 v3
du_pw'45'just'45'inv_882 ::
  Maybe
    (Integer ->
     [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pw'45'just'45'inv_882 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-sound
d_accept'45'sound_896 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'sound_896 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6
  = du_accept'45'sound_896 v2 v4
du_accept'45'sound_896 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'sound_896 v0 v1
  = coe du_'10214''10215''8869''45'sound_368 (coe v1) (coe v0)
-- Once.Adequacy.Compile.WithCPU.Typed
d_Typed_916 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) -> ()
d_Typed_916 = erased
-- Once.Adequacy.Compile.WithCPU._⊢R_
d__'8866'R__922 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d__'8866'R__922 = erased
-- Once.Adequacy.Compile.WithCPU.main-realize-agrees
d_main'45'realize'45'agrees_942 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'realize'45'agrees_942 = erased
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ˢ
d_'10214'_'10215''738'_946 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_'10214'_'10215''738'_946 ~v0 ~v1 v2 v3
  = du_'10214'_'10215''738'_946 v2 v3
du_'10214'_'10215''738'_946 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_'10214'_'10215''738'_946 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Adequacy.MainExtract.du_runMain'738'_20
                    (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v0))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Adequacy.ModuleComplete.d_mainRealized_674
                          (coe v2) (coe v4) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.sd-bridge
d_sd'45'bridge_960 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'bridge_960 = erased
-- Once.Adequacy.Compile.WithCPU.pw-just-rel
d_pw'45'just'45'rel_978 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45'just'45'rel_978 = erased
-- Once.Adequacy.Compile.WithCPU.compile-just-ir
d_compile'45'just'45'ir_994 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_994 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_compile'45'just'45'ir_994 v5
du_compile'45'just'45'ir_994 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'just'45'ir_994 v0
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
d_c'8801'n_1050 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_1050 = erased
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-just-adm
d_'10214''10215''8869''45'just'45'adm_1066 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just'45'adm_1066 = erased
-- Once.Adequacy.Compile.WithCPU.⟦⟧⊥-just
d_'10214''10215''8869''45'just_1090 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_1090 = erased
-- Once.Adequacy.Compile.WithCPU._.go
d_go_1112 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1112 = erased
-- Once.Adequacy.Compile.WithCPU.admissible-resolve
d_admissible'45'resolve_1134 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_admissible'45'resolve_1134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_admissible'45'resolve_1134 v7
du_admissible'45'resolve_1134 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_admissible'45'resolve_1134 v0 = coe v0
-- Once.Adequacy.Compile.WithCPU.admissible-unresolve
d_admissible'45'unresolve_1156 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_admissible'45'unresolve_1156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_admissible'45'unresolve_1156 v7
du_admissible'45'unresolve_1156 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_admissible'45'unresolve_1156 v0 = coe v0
-- Once.Adequacy.Compile.WithCPU.correctR-sound
d_correctR'45'sound_1180 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'sound_1180 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6
  = du_correctR'45'sound_1180 v2 v4
du_correctR'45'sound_1180 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'sound_1180 v0 v1
  = let v2
          = coe
              du_'10214''10215''8869''45'm'45'sound_346
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_70
                 (coe
                    MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14 (coe v1))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_66
                    (coe
                       MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                         (coe v1))))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                            (coe v1)))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                              (coe v1))))))))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Parser.Module.d_r_370
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
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
                                   MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                            (coe v1))))
                                   (coe
                                      MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                      (coe
                                         MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                            (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                               (coe v1)))))
                                   (\ v2 v3 v4 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                        (coe
                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                 (coe v1))))))))))))
              (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> let v7
                           = MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR'45'aux_48
                               (coe
                                  MAlonzo.Code.Once.Compile.d_compileResolvedModule'45'aux_554
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)
                                  (coe
                                     MAlonzo.Code.Once.Parser.d_guardDistinct_526
                                     (coe
                                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v3))
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v3))
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> let v9
                                     = coe
                                         MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_130
                                         (coe
                                            MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                              (coe v1))))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                 (coe v1)))))
                                                     (\ v9 v10 v11 ->
                                                        coe
                                                          MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                   (coe v1))))))))
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.d_r_370
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
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
                                                        MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                 (coe v1))))
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                 (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                    (coe v1)))))
                                                        (\ v9 v10 v11 ->
                                                           coe
                                                             MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                      (coe v1)))))))))) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                      -> coe
                                           seq (coe v11)
                                           (let v12
                                                  = coe
                                                      MAlonzo.Code.Once.Adequacy.CanonReflectModule.du_go_144
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14
                                                         (coe v1))
                                                      (coe v10) (coe v3) (coe v6)
                                                      (coe
                                                         MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_926
                                                         (coe v3) (coe v6) (coe v8))
                                                      (coe
                                                         MAlonzo.Code.Once.Adequacy.CanonResolve.d_noImports'63'_16
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                            (coe v10))) in
                                            coe
                                              (coe
                                                 seq (coe v12)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v10) (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_496
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                             (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             du_accept'45'gm_750 (coe v0) (coe v3))
                                                          erased)))))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> let v8 = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12 in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11
                                               = coe
                                                   MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_130
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                        (coe v1))))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                           (coe v1)))))
                                                               (\ v11 v12 v13 ->
                                                                  coe
                                                                    MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                          (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                             (coe v1))))))))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.d_r_370
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
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
                                                                  MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                           (coe v1))))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                              (coe v1)))))
                                                                  (\ v11 v12 v13 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_606
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                             (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                                (coe v1)))))))))) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                -> coe
                                                     seq (coe v13)
                                                     (let v14
                                                            = coe
                                                                MAlonzo.Code.Once.Adequacy.CanonReflectModule.du_go_144
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_14
                                                                   (coe v1))
                                                                (coe v12) (coe v3) (coe v6)
                                                                (coe
                                                                   MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_926
                                                                   (coe v3) (coe v6) (coe v9))
                                                                (coe
                                                                   MAlonzo.Code.Once.Adequacy.CanonResolve.d_noImports'63'_16
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                                      (coe v12))) in
                                                      coe
                                                        (coe
                                                           seq (coe v14)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v12) (coe v14))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_496
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcText_16
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       du_accept'45'gm_750 (coe v0)
                                                                       (coe v3))
                                                                    erased)))))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.WithCPU.correctR-complete
d_correctR'45'complete_1330 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_1330 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_correctR'45'complete_1330 v0 v2 v3 v4 v5
du_correctR'45'complete_1330 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'complete_1330 v0 v1 v2 v3 v4
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
                                                          MAlonzo.Code.Once.Adequacy.MainBuilds.du_cfm'45'built'45'aux_630
                                                          (coe v1) (coe v10)
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
                                                               du_string'45'to'45'bytes_144 v0 v1
                                                               v18)
                                                            erased
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.p-eq
d_p'45'eq_1448 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'45'eq_1448 = erased
-- Once.Adequacy.Compile.WithCPU._.stm-eq
d_stm'45'eq_1450 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stm'45'eq_1450 = erased
-- Once.Adequacy.Compile.WithCPU._.c≡j
d_c'8801'j_1452 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'j_1452 = erased
-- Once.Adequacy.Compile.WithCPU.correctR
d_correctR_1480 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR_1480 v0 ~v1 v2 v3 v4 = du_correctR_1480 v0 v2 v3 v4
du_correctR_1480 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR_1480 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v4 v5 -> coe du_correctR'45'sound_1180 (coe v1) (coe v3))
      (\ v4 v5 v6 ->
         coe
           du_correctR'45'complete_1330 (coe v0) (coe v1) (coe v2) (coe v3)
           v4)
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ᵈ
d_'10214'_'10215''7496'_1498 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_'10214'_'10215''7496'_1498 ~v0 ~v1 v2 v3
  = du_'10214'_'10215''7496'_1498 v2 v3
du_'10214'_'10215''7496'_1498 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_'10214'_'10215''7496'_1498 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Denotation.MainMeaning.d_meaning'7496'_170
                    (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v0))
                    (coe v2) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.bridgeᵈ
d_bridge'7496'_1514 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'7496'_1514 = erased
-- Once.Adequacy.Compile.WithCPU.Admissible
d_Admissible_1526 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Admissible_1526 = erased
-- Once.Adequacy.Compile.WithCPU.correctᵈ
d_correct'7496'_1546 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_48) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_1546 v0 ~v1 v2 v3 v4
  = du_correct'7496'_1546 v0 v2 v3 v4
du_correct'7496'_1546 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correct'7496'_1546 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v4 v5 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe du_correctR'45'sound_1180 (coe v1) (coe v3)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_correctR'45'sound_1180 (coe v1) (coe v3))))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe du_correctR'45'sound_1180 (coe v1) (coe v3)))))
                    erased))))
      (\ v4 v5 v6 ->
         coe
           du_correctR'45'complete_1330 (coe v0) (coe v1) (coe v2) (coe v3)
           v4)
