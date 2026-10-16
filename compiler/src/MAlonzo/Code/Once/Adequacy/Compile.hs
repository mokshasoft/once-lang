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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.CPU
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.CoreBridge
import qualified MAlonzo.Code.Once.Adequacy.FrontEndBridge
import qualified MAlonzo.Code.Once.Adequacy.MainBuilds
import qualified MAlonzo.Code.Once.Adequacy.ModuleComplete
import qualified MAlonzo.Code.Once.Adequacy.ResolveBridge
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Admissible
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.Meaning
import qualified MAlonzo.Code.Once.Lang.Core.Telescope
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Resolution
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1078
d_compile'45'asm_6 v0 v1
  = let v2
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_256
              (coe
                 MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50 (coe v1))
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_252
                 (coe
                    MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v1)))
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v1)))
                                   (coe (0 :: Integer))))
                             (\ v2 v3 v4 ->
                                coe
                                  MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                  (coe
                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                           (coe v1)))
                                     (coe (0 :: Integer)))))))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Parser.Module.d_r_370
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v1)))
                                (coe (0 :: Integer))))))
                    (coe
                       MAlonzo.Code.Once.Parser.d_allTrailing_18
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v1)))
                                   (coe (0 :: Integer)))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                            (coe v1)))
                                      (coe (0 :: Integer))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                              (coe v1)))
                                        (coe (0 :: Integer)))))))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1338
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_1076)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Compile.C_Error_1086
                (coe
                   ("front-end (parse / import resolution) failed" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.compile-cli-asm
d_compile'45'cli'45'asm_26 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Compile.T_Stage_1070 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1078
d_compile'45'cli'45'asm_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_1338 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.⟦_⟧M
d_'10214'_'10215'M_38 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215'M_38 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_236
      (coe MAlonzo.Code.Once.Compile.d_moduleToProgram_880 (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.AsmWF-of
d_AsmWF'45'of_48 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> AgdaAny -> ()
d_AsmWF'45'of_48 = erased
-- Once.Adequacy.Compile.run-file
d_run'45'file_52 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_run'45'file_52 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.CPU.Interface.d_run'45'trace_46
         (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6 (coe v0)) v1
         v2
         (coe
            MAlonzo.Code.Once.Adequacy.CPU.Interface.d_initialState_42
            (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6 (coe v0))
            v2))
-- Once.Adequacy.Compile.file-bytes
d_file'45'bytes_68 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  AgdaAny -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_file'45'bytes_68 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_50
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_printFile_964 v0 v1)
-- Once.Adequacy.Compile.exec-file
d_exec'45'file_80 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'file_80 = erased
-- Once.Adequacy.Compile.ArchCorrect
d_ArchCorrect_104 a0 a1 = ()
data T_ArchCorrect_104
  = C_constructor_178 (MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                       MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6)
                      (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
                       AgdaAny ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
-- Once.Adequacy.Compile.ArchCorrect.flat-trace
d_flat'45'trace_146 ::
  T_ArchCorrect_104 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'trace_146 v0
  = case coe v0 of
      C_constructor_178 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.file-wf
d_file'45'wf_152 ::
  T_ArchCorrect_104 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_file'45'wf_152 v0
  = case coe v0 of
      C_constructor_178 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.file-trace-correct
d_file'45'trace'45'correct_168 ::
  T_ArchCorrect_104 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_file'45'trace'45'correct_168 = erased
-- Once.Adequacy.Compile.ArchCorrect.ir-flat-correct
d_ir'45'flat'45'correct_176 ::
  T_ArchCorrect_104 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct_176 = erased
-- Once.Adequacy.Compile.build≡file-ef
d_build'8801'file'45'ef_188 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_build'8801'file'45'ef_188 = erased
-- Once.Adequacy.Compile.build≡file
d_build'8801'file_212 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_build'8801'file_212 = erased
-- Once.Adequacy.Compile.built-of-inv
d_built'45'of'45'inv_228 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_built'45'of'45'inv_228 ~v0 v1 ~v2 ~v3
  = du_built'45'of'45'inv_228 v1
du_built'45'of'45'inv_228 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_built'45'of'45'inv_228 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_252 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gmoduleToModule'45'correct_252 = erased
-- Once.Adequacy.Compile.WithCPU.compile-fe
d_compile'45'fe_278 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'fe_278 ~v0 v1 v2 = du_compile'45'fe_278 v1 v2
du_compile'45'fe_278 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'fe_278 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_file'45'bytes_68 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-mir
d_compile'45'mir_286 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_286 ~v0 v1 v2 v3 v4
  = du_compile'45'mir_286 v1 v2 v3 v4
du_compile'45'mir_286 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_286 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_compile'45'fe_278 (coe v0)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFileFromModule_1270
                (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v1) (coe v0) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-gm
d_compile'45'gm_300 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_300 ~v0 v1 v2 v3 = du_compile'45'gm_300 v1 v2 v3
du_compile'45'gm_300 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_300 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_compile'45'mir_286 (coe v0) (coe v1) (coe v3)
             (coe MAlonzo.Code.Once.Compile.d_moduleToIR_836 (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile
d_compile_312 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_312 ~v0 v1 v2 v3 = du_compile_312 v1 v2 v3
du_compile_312 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_312 v0 v1 v2
  = coe
      du_compile'45'gm_300 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_264 (coe v2))
-- Once.Adequacy.Compile.WithCPU.refuse-gated
d_refuse'45'gated_330 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gated_330 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-ef
d_refuse'45'ef_362 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'ef_362 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-mir
d_refuse'45'mir_392 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'mir_392 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-gm
d_refuse'45'gm_418 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gm_418 = erased
-- Once.Adequacy.Compile.WithCPU.accept-gated
d_accept'45'gated_440 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gated_440 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_accept'45'gated_440 v5
du_accept'45'gated_440 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gated_440 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-ef
d_accept'45'ef_472 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'ef_472 ~v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_accept'45'ef_472 v1 v3 v4
du_accept'45'ef_472 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'ef_472 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'gated_440
         (coe
            MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
            (coe v0) (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-mir
d_accept'45'mir_502 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'mir_502 ~v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_accept'45'mir_502 v1 v3 v4
du_accept'45'mir_502 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'mir_502 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'ef_472 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Parser.d_extractFunctions_550
            (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
            (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-gm
d_accept'45'gm_528 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gm_528 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_accept'45'gm_528 v1 v3
du_accept'45'gm_528 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gm_528 v0 v1
  = coe
      du_accept'45'mir_502 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Compile.d_moduleToIR_836 (coe v1))
-- Once.Adequacy.Compile.WithCPU._≋_
d__'8779'__538 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 -> ()
d__'8779'__538 = erased
-- Once.Adequacy.Compile.WithCPU.compile-just-ir
d_compile'45'just'45'ir_558 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_558 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7
  = du_compile'45'just'45'ir_558 v4
du_compile'45'just'45'ir_558 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'just'45'ir_558 v0
  = let v1
          = MAlonzo.Code.Once.Compile.d_moduleToIR'45'aux_832
              (coe
                 MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_712
                 (coe MAlonzo.Code.Once.IR.C_Heap_8)
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                 (coe
                    MAlonzo.Code.Once.Parser.d_guardDistinct_538
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.WithCPU._.c≡n
d_c'8801'n_614 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_614 = erased
-- Once.Adequacy.Compile.WithCPU.correctR-complete
d_correctR'45'complete_634 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_634 ~v0 v1 v2 ~v3 v4 v5 ~v6
  = du_correctR'45'complete_634 v1 v2 v4 v5
du_correctR'45'complete_634 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'complete_634 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           seq (coe v9)
                           (let v10
                                  = let v10
                                          = MAlonzo.Code.Once.Parser.d_guardDistinct_538
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                    (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                    (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
                                    coe
                                      (case coe v10 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                           -> let v12
                                                    = MAlonzo.Code.Once.Adequacy.ModuleComplete.d_ce'45'find'45'complete_306
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_emptyCScope_388)
                                                        (coe v11) (coe v6)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe v7))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe v7)) in
                                              coe
                                                (case coe v12 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                     -> case coe v14 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                            -> coe
                                                                 seq (coe v16)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v15) erased)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError) in
                            coe
                              (coe
                                 seq (coe v10)
                                 (let v11
                                        = coe
                                            MAlonzo.Code.Once.Adequacy.MainBuilds.du_cfm'45'built'45'aux_584
                                            (coe v0) (coe v4)
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_guardDistinct_538
                                               (coe
                                                  MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                     (coe v4))
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                     (coe v4))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Once.Adequacy.MainBuilds.du_crm'45'doOpt_520
                                                  (coe v1) (coe v4)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.MainBuilds.du_moduleToIR'45'inj'8322'_648
                                                        (coe v4))))) in
                                  coe
                                    (coe
                                       seq (coe v11)
                                       (let v12
                                              = coe
                                                  du_built'45'of'45'inv_228
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_cfm'45'file'45'ef_1246
                                                     (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v1)
                                                     (coe v0) (coe v4)
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.d_guardDistinct_538
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                              (coe v4))
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                              (coe v4))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
                                        coe
                                          (case coe v12 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                               -> coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe d_file'45'bytes_68 (coe v0) (coe v13))
                                                    erased
                                             _ -> MAlonzo.RTE.mazUnreachableError))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.p-eq
d_p'45'eq_756 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'45'eq_756 = erased
-- Once.Adequacy.Compile.WithCPU._.res-eq
d_res'45'eq_758 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'eq_758 = erased
-- Once.Adequacy.Compile.WithCPU._.stm-eq
d_stm'45'eq_760 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stm'45'eq_760 = erased
-- Once.Adequacy.Compile.WithCPU._.c≡j
d_c'8801'j_762 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'j_762 = erased
-- Once.Adequacy.Compile.WithCPU.accept-typed-aux
d_accept'45'typed'45'aux_788 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'typed'45'aux_788 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7
  = du_accept'45'typed'45'aux_788 v5 v6
du_accept'45'typed'45'aux_788 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'typed'45'aux_788 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_586
                   (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.c≡n
d_c'8801'n_806 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_806 = erased
-- Once.Adequacy.Compile.WithCPU.accept-typed
d_accept'45'typed_836 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'typed_836 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_accept'45'typed_836 v3
du_accept'45'typed_836 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'typed_836 v0
  = coe
      du_accept'45'typed'45'aux_788
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_264 (coe v0))
      erased
-- Once.Adequacy.Compile.WithCPU.Admissible
d_Admissible_848 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Admissible_848 = erased
-- Once.Adequacy.Compile.WithCPU.sigOfT
d_sigOfT_854 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigOfT_854 ~v0 v1 = du_sigOfT_854 v1
du_sigOfT_854 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_sigOfT_854 v0
  = coe
      MAlonzo.Code.Once.Lang.Module.d_moduleSig_132
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
-- Once.Adequacy.Compile.WithCPU.core-run
d_core'45'run_864 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
d_core'45'run_864 ~v0 v1 v2 v3 = du_core'45'run_864 v1 v2 v3
du_core'45'run_864 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  Integer -> [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56]
du_core'45'run_864 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.d_runProgram_146
      (coe MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedSig_24 (coe v1))
      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedProgram_52 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.WithCPU.ir-core
d_ir'45'core_882 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'core_882 = erased
-- Once.Adequacy.Compile.WithCPU.runProgram-pf
d_runProgram'45'pf_910 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
d_runProgram'45'pf_910 ~v0 v1 v2 v3 v4
  = du_runProgram'45'pf_910 v1 v2 v3 v4
du_runProgram'45'pf_910 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
du_runProgram'45'pf_910 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Core.Telescope.C_program_124 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_events'8734''45'pf_1392
             (coe MAlonzo.Code.Once.Lang.Trace.C_interp_192 (coe v0) (coe v3))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                MAlonzo.Code.Once.Lang.Core.Telescope.du_runEntry_136
                (coe
                   MAlonzo.Code.Once.Lang.Core.Meaning.d_defs_378
                   (MAlonzo.Code.Once.Lang.Core.Telescope.d_teleSem_36
                      (coe v0) (coe v4) (coe v5) (coe v1) (coe v3) (coe v6))
                   v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ᵈᴵ
d_'10214'_'10215''7496''7477'_926 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''7496''7477'_926 ~v0 v1 v2 v3
  = du_'10214'_'10215''7496''7477'_926 v1 v2 v3
du_'10214'_'10215''7496''7477'_926 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''7496''7477'_926 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.C_mkBehavior_40
      (coe du_core'45'run_864 (coe v0) (coe v1) (coe v2))
      (MAlonzo.Code.Once.Lang.Trace.d_coh_490
         (coe du_pf_938 (coe v0) (coe v1) (coe v2)))
      (MAlonzo.Code.Once.Lang.Trace.d_bnd_486
         (coe du_pf_938 (coe v0) (coe v1) (coe v2)))
-- Once.Adequacy.Compile.WithCPU._.pf
d_pf_938 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
d_pf_938 ~v0 v1 v2 v3 = du_pf_938 v1 v2 v3
du_pf_938 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_260 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
du_pf_938 v0 v1 v2
  = coe
      du_runProgram'45'pf_910
      (coe MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedSig_24 (coe v1))
      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedProgram_52 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.WithCPU._.exec
d_exec_946 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_exec_946 ~v0 v1 v2 v3 = du_exec_946 v1 v2 v3
du_exec_946 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_exec_946 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_72
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6 (coe v1))
      (coe v0) (coe v2)
-- Once.Adequacy.Compile.WithCPU._.file-correct
d_file'45'correct_962 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_file'45'correct_962 = erased
-- Once.Adequacy.Compile.WithCPU._._.P
d_P_984 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_P_984 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 = du_P_984 v3 v5
du_P_984 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_P_984 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_868 (coe v0)) (coe v1)
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_990 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869''45'ir_990 ~v0 v1 v2 v3
  = du_'10214'_'10215''8869''45'ir_990 v1 v2 v3
du_'10214'_'10215''8869''45'ir_990 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869''45'ir_990 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_236
                (coe v1)
                (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v2))
                (coe v0))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-adm
d_'10214'_'10215''8869''45'adm_1000 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869''45'adm_1000 ~v0 v1 v2 v3 v4
  = du_'10214'_'10215''8869''45'adm_1000 v1 v2 v3 v4
du_'10214'_'10215''8869''45'adm_1000 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869''45'adm_1000 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_'10214'_'10215''8869''45'ir_990 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Compile.d_programAt_872
                          (coe MAlonzo.Code.Once.Compile.d_moduleTable_868 (coe v1))
                          (coe MAlonzo.Code.Once.Compile.d_moduleToIR_836 (coe v1)))
                       (coe v2))
             else coe
                    seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_1010 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869''45'm_1010 ~v0 v1 v2 v3
  = du_'10214'_'10215''8869''45'm_1010 v1 v2 v3
du_'10214'_'10215''8869''45'm_1010 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869''45'm_1010 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_'10214'_'10215''8869''45'adm_1000 (coe v0) (coe v3) (coe v2)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥
d_'10214'_'10215''8869'_1016 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869'_1016 ~v0 v1 v2 v3
  = du_'10214'_'10215''8869'_1016 v1 v2 v3
du_'10214'_'10215''8869'_1016 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869'_1016 v0 v1 v2
  = coe
      du_'10214'_'10215''8869''45'm_1010 (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_264 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_1032 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_1032 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                           ~v6
  = du_'10214''10215''8869''45'ir'45'sound_1032 v3
du_'10214''10215''8869''45'ir'45'sound_1032 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'ir'45'sound_1032 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-adm-sound
d_'10214''10215''8869''45'adm'45'sound_1058 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'10214''10215''8869''45'adm'45'sound_1058 ~v0 ~v1 v2 ~v3 v4 ~v5
                                            ~v6
  = du_'10214''10215''8869''45'adm'45'sound_1058 v2 v4
du_'10214''10215''8869''45'adm'45'sound_1058 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_'10214''10215''8869''45'adm'45'sound_1058 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_586
                   (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_1082 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_1082 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'10214''10215''8869''45'm'45'sound_1082 v2 v3
du_'10214''10215''8869''45'm'45'sound_1082 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'm'45'sound_1082 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   du_'10214''10215''8869''45'adm'45'sound_1058 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                      (coe v1) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_1104 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_1104 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'10214''10215''8869''45'sound_1104 v2 v3
du_'10214''10215''8869''45'sound_1104 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'sound_1104 v0 v1
  = coe
      du_'10214''10215''8869''45'm'45'sound_1082
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_264 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU._.opt-trace
d_opt'45'trace_1124
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.Compile.WithCPU._.opt-trace"
-- Once.Adequacy.Compile.WithCPU._.TraceAt
d_TraceAt_1126 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_1126 = erased
-- Once.Adequacy.Compile.WithCPU._.correct-fe
d_correct'45'fe_1148 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'fe_1148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 v10
  = du_correct'45'fe_1148 v6 v8 v10
du_correct'45'fe_1148 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'fe_1148 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_just_40
             (coe v2 v3 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-mir
d_correct'45'mir_1196 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_1196 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_correct'45'mir_1196 v2 v3 v4 v5
du_correct'45'mir_1196 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'mir_1196 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_correct'45'fe_1148
             (coe
                MAlonzo.Code.Once.Compile.d_compileFileFromModule_1270
                (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v1) (coe v0) (coe v2))
             erased erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-gm
d_correct'45'gm_1234 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm_1234 ~v0 ~v1 v2 v3 v4 ~v5
  = du_correct'45'gm_1234 v2 v3 v4
du_correct'45'gm_1234 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm_1234 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_correct'45'gm'45'adm_1246 (coe v0) (coe v1) (coe v3)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v0) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-gm-adm
d_correct'45'gm'45'adm_1246 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm'45'adm_1246 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_correct'45'gm'45'adm_1246 v2 v3 v4 v5
du_correct'45'gm'45'adm_1246 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm'45'adm_1246 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_correct'45'mir_1196 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.Compile.d_moduleToIR_836 (coe v2)))
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct
d_correct_1302 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_1302 ~v0 ~v1 v2 v3 v4 ~v5 = du_correct_1302 v2 v3 v4
du_correct_1302 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_1302 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         du_correct'45'gm_1234 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_264 (coe v2)))
-- Once.Adequacy.Compile.WithCPU._.pw-just-inv
d_pw'45'just'45'inv_1350 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_1350 ~v0 ~v1 ~v2 v3 ~v4
  = du_pw'45'just'45'inv_1350 v3
du_pw'45'just'45'inv_1350 ::
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pw'45'just'45'inv_1350 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.pw-just-rel
d_pw'45'just'45'rel_1358 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45'just'45'rel_1358 = erased
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-just-adm
d_'10214''10215''8869''45'just'45'adm_1368 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just'45'adm_1368 = erased
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-just
d_'10214''10215''8869''45'just_1392 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_1392 = erased
-- Once.Adequacy.Compile.WithCPU._._.go
d_go_1414 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1414 = erased
-- Once.Adequacy.Compile.WithCPU._.sound-trace
d_sound'45'trace_1444 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sound'45'trace_1444 = erased
-- Once.Adequacy.Compile.WithCPU._._.ls′
d_ls'8242'_1474 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ls'8242'_1474 = erased
-- Once.Adequacy.Compile.WithCPU._._.p
d_p_1480 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_p_1480 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_p_1480 v2 v3 v4
du_p_1480 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_p_1480 v0 v1 v2 = coe du_correct_1302 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU._._.admR
d_admR_1484 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_admR_1484 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_admR_1484 v2 v7
du_admR_1484 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_admR_1484 v0 v1 = coe du_accept'45'gm_528 (coe v0) (coe v1)
-- Once.Adequacy.Compile.WithCPU._._.p'
d_p''_1486 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_p''_1486 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_p''_1486 v2 v3 v4
du_p''_1486 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_p''_1486 v0 v1 v2 = coe du_p_1480 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU._._.e≋
d_e'8779'_1490 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e'8779'_1490 = erased
-- Once.Adequacy.Compile.WithCPU.correctᵈ
d_correct'7496'_1508 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_1508 ~v0 v1 v2 v3 = du_correct'7496'_1508 v1 v2 v3
du_correct'7496'_1508 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correct'7496'_1508 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v3 v4 -> coe du_sound_1526 (coe v0) (coe v2))
      (\ v3 v4 v5 ->
         coe du_correctR'45'complete_634 (coe v0) (coe v1) v3 v4)
-- Once.Adequacy.Compile.WithCPU._.sound
d_sound_1526 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_104) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sound_1526 ~v0 v1 ~v2 v3 ~v4 ~v5 = du_sound_1526 v1 v3
du_sound_1526 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sound_1526 v0 v1
  = let v2
          = coe
              du_accept'45'typed'45'aux_788
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_256
                 (coe
                    MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50 (coe v1))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_252
                    (coe
                       MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v1)))
                                   (coe (0 :: Integer)))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                            (coe v1)))
                                      (coe (0 :: Integer))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                              (coe v1)))
                                        (coe (0 :: Integer)))))))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Parser.Module.d_r_370
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v1)))
                                   (coe (0 :: Integer))))))
                       (coe
                          MAlonzo.Code.Once.Parser.d_allTrailing_18
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                            (coe v1)))
                                      (coe (0 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                      (coe
                                         MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                            (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                               (coe v1)))
                                         (coe (0 :: Integer))))
                                   (\ v2 v3 v4 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                        (coe
                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                 (coe v1)))
                                           (coe (0 :: Integer)))))))))))
              erased in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> let v7
                           = MAlonzo.Code.Once.Compile.d_moduleToIR'45'aux_832
                               (coe
                                  MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_712
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                  (coe
                                     MAlonzo.Code.Once.Parser.d_guardDistinct_538
                                     (coe
                                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v3))
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v3))
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> let v9
                                     = coe
                                         MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_316
                                         (coe
                                            MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                              (coe v1)))
                                                        (coe (0 :: Integer)))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                 (coe v1)))
                                                           (coe (0 :: Integer))))
                                                     (\ v9 v10 v11 ->
                                                        coe
                                                          MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                   (coe v1)))
                                                             (coe (0 :: Integer)))))))
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.d_r_370
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                              (coe v1)))
                                                        (coe (0 :: Integer))))))
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_allTrailing_18
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                 (coe v1)))
                                                           (coe (0 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                 (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                    (coe v1)))
                                                              (coe (0 :: Integer))))
                                                        (\ v9 v10 v11 ->
                                                           coe
                                                             MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                      (coe v1)))
                                                                (coe (0 :: Integer))))))))) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                      -> coe
                                           seq (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v3)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_780
                                                       (coe v3) (coe v6) (coe v8))))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v10)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_448
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                             (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Once.Adequacy.ResolveBridge.du_resolvesModule'45'complete_2092
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50
                                                             (coe v1))
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                             (coe v10)))))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe du_accept'45'gm_528 (coe v0) (coe v3))
                                                    erased)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> let v8 = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12 in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11
                                               = coe
                                                   MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_316
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                        (coe v1)))
                                                                  (coe (0 :: Integer)))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                           (coe v1)))
                                                                     (coe (0 :: Integer))))
                                                               (\ v11 v12 v13 ->
                                                                  coe
                                                                    MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                          (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                             (coe v1)))
                                                                       (coe (0 :: Integer)))))))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.d_r_370
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                        (coe v1)))
                                                                  (coe (0 :: Integer))))))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_allTrailing_18
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                           (coe v1)))
                                                                     (coe (0 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                              (coe v1)))
                                                                        (coe (0 :: Integer))))
                                                                  (\ v11 v12 v13 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                             (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                                (coe v1)))
                                                                          (coe
                                                                             (0 ::
                                                                                Integer))))))))) in
                                         coe
                                           (case coe v11 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                -> coe
                                                     seq (coe v13)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v3)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v6)
                                                              (coe
                                                                 MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_780
                                                                 (coe v3) (coe v6) (coe v9))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v12)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_448
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.ResolveBridge.du_resolvesModule'45'complete_2092
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50
                                                                       (coe v1))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                                       (coe v12)))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 du_accept'45'gm_528 (coe v0)
                                                                 (coe v3))
                                                              erased)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
