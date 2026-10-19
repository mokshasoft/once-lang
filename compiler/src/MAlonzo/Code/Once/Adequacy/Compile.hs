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
import qualified MAlonzo.Code.Once.Adequacy.RewritePreserves
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Admissible
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceTr
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.Telescope
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Resolution
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Metatheory.Trace
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1298
d_compile'45'asm_6 v0 v1
  = let v2
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_254
              (coe
                 MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50 (coe v1))
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_250
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
                MAlonzo.Code.Once.Compile.d_compileFromModule_1558
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_1296)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Compile.C_Error_1306
                (coe
                   ("front-end (parse / import resolution) failed" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.compile-cli-asm
d_compile'45'cli'45'asm_26 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Compile.T_Stage_1290 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1298
d_compile'45'cli'45'asm_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_1558 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.AsmWF-of
d_AsmWF'45'of_40 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> AgdaAny -> ()
d_AsmWF'45'of_40 = erased
-- Once.Adequacy.Compile.run-file
d_run'45'file_44 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_run'45'file_44 v0 v1 v2
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
d_file'45'bytes_60 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  AgdaAny -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_file'45'bytes_60 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_50
      (MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_printFile_1184 v0 v1)
-- Once.Adequacy.Compile.exec-file
d_exec'45'file_72 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'file_72 = erased
-- Once.Adequacy.Compile.ArchCorrect
d_ArchCorrect_96 a0 a1 = ()
data T_ArchCorrect_96
  = C_constructor_138 (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
                       AgdaAny ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                      (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
                       AgdaAny ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Once.IR.T_IR_16 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86)
-- Once.Adequacy.Compile.ArchCorrect.file-wf
d_file'45'wf_124 ::
  T_ArchCorrect_96 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_file'45'wf_124 v0
  = case coe v0 of
      C_constructor_138 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.file-tr
d_file'45'tr_136 ::
  T_ArchCorrect_96 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_file'45'tr_136 v0
  = case coe v0 of
      C_constructor_138 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.build≡file-ef
d_build'8801'file'45'ef_148 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_build'8801'file'45'ef_148 = erased
-- Once.Adequacy.Compile.build≡file
d_build'8801'file_172 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_build'8801'file_172 = erased
-- Once.Adequacy.Compile.built-of-inv
d_built'45'of'45'inv_188 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_built'45'of'45'inv_188 ~v0 v1 ~v2 ~v3
  = du_built'45'of'45'inv_188 v1
du_built'45'of'45'inv_188 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_built'45'of'45'inv_188 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-fe
d_compile'45'fe_212 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'fe_212 ~v0 v1 v2 = du_compile'45'fe_212 v1 v2
du_compile'45'fe_212 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'fe_212 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe d_file'45'bytes_60 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-mir
d_compile'45'mir_220 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_220 ~v0 v1 v2 v3 v4
  = du_compile'45'mir_220 v1 v2 v3 v4
du_compile'45'mir_220 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_220 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_compile'45'fe_212 (coe v0)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFileFromModule_1490
                (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v1) (coe v0) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-gm
d_compile'45'gm_234 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_234 ~v0 v1 v2 v3 = du_compile'45'gm_234 v1 v2 v3
du_compile'45'gm_234 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_234 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_compile'45'mir_220 (coe v0) (coe v1) (coe v3)
             (coe MAlonzo.Code.Once.Compile.d_moduleToIR_1052 (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile
d_compile_246 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_246 ~v0 v1 v2 v3 = du_compile_246 v1 v2 v3
du_compile_246 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_246 v0 v1 v2
  = coe
      du_compile'45'gm_234 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_262 (coe v2))
-- Once.Adequacy.Compile.WithCPU.refuse-gated
d_refuse'45'gated_264 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gated_264 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-ef
d_refuse'45'ef_296 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'ef_296 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-mir
d_refuse'45'mir_326 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'mir_326 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-gm
d_refuse'45'gm_352 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gm_352 = erased
-- Once.Adequacy.Compile.WithCPU.accept-gated
d_accept'45'gated_374 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gated_374 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_accept'45'gated_374 v5
du_accept'45'gated_374 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gated_374 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-ef
d_accept'45'ef_406 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'ef_406 ~v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_accept'45'ef_406 v1 v3 v4
du_accept'45'ef_406 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'ef_406 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'gated_374
         (coe
            MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
            (coe v0) (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-mir
d_accept'45'mir_436 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'mir_436 ~v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_accept'45'mir_436 v1 v3 v4
du_accept'45'mir_436 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'mir_436 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'ef_406 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Parser.d_extractFunctions_550
            (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
            (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-gm
d_accept'45'gm_462 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gm_462 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_accept'45'gm_462 v1 v3
du_accept'45'gm_462 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gm_462 v0 v1
  = coe
      du_accept'45'mir_436 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Compile.d_moduleToIR_1052 (coe v1))
-- Once.Adequacy.Compile.WithCPU._≋_
d__'8779'__472 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 -> ()
d__'8779'__472 = erased
-- Once.Adequacy.Compile.WithCPU.compile-just-ir
d_compile'45'just'45'ir_490 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_490 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7
  = du_compile'45'just'45'ir_490 v4
du_compile'45'just'45'ir_490 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'just'45'ir_490 v0
  = let v1
          = MAlonzo.Code.Once.Compile.d_moduleToIR'45'aux_1048
              (coe
                 MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_830
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
d_c'8801'n_546 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_546 = erased
-- Once.Adequacy.Compile.WithCPU.correctR-complete
d_correctR'45'complete_566 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_566 ~v0 v1 v2 ~v3 v4 v5 ~v6
  = du_correctR'45'complete_566 v1 v2 v4 v5
du_correctR'45'complete_566 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'complete_566 v0 v1 v2 v3
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
                                                    = MAlonzo.Code.Once.Adequacy.ModuleComplete.d_ce'45'find'45'complete_316
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_emptyCScope_448)
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
                                            MAlonzo.Code.Once.Adequacy.MainBuilds.du_cfm'45'built'45'aux_724
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
                                                  MAlonzo.Code.Once.Adequacy.MainBuilds.du_crm'45'doOpt_660
                                                  (coe v1) (coe v4)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.MainBuilds.du_moduleToIR'45'inj'8322'_788
                                                        (coe v4))))) in
                                  coe
                                    (coe
                                       seq (coe v11)
                                       (let v12
                                              = coe
                                                  du_built'45'of'45'inv_188
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_cfm'45'file'45'ef_1466
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
                                                    (coe d_file'45'bytes_60 (coe v0) (coe v13))
                                                    erased
                                             _ -> MAlonzo.RTE.mazUnreachableError))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.p-eq
d_p'45'eq_688 ::
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
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'45'eq_688 = erased
-- Once.Adequacy.Compile.WithCPU._.res-eq
d_res'45'eq_690 ::
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
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'eq_690 = erased
-- Once.Adequacy.Compile.WithCPU._.stm-eq
d_stm'45'eq_692 ::
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
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stm'45'eq_692 = erased
-- Once.Adequacy.Compile.WithCPU._.c≡j
d_c'8801'j_694 ::
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
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'j_694 = erased
-- Once.Adequacy.Compile.WithCPU.accept-typed-aux
d_accept'45'typed'45'aux_720 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'typed'45'aux_720 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7
  = du_accept'45'typed'45'aux_720 v5 v6
du_accept'45'typed'45'aux_720 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'typed'45'aux_720 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_620
                   (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.c≡n
d_c'8801'n_738 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_738 = erased
-- Once.Adequacy.Compile.WithCPU.accept-typed
d_accept'45'typed_768 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'typed_768 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_accept'45'typed_768 v3
du_accept'45'typed_768 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'typed_768 v0
  = coe
      du_accept'45'typed'45'aux_720
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_262 (coe v0))
      erased
-- Once.Adequacy.Compile.WithCPU.Admissible
d_Admissible_780 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Admissible_780 = erased
-- Once.Adequacy.Compile.WithCPU.sigOfT
d_sigOfT_786 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigOfT_786 ~v0 v1 = du_sigOfT_786 v1
du_sigOfT_786 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_sigOfT_786 v0
  = coe
      MAlonzo.Code.Once.Lang.Module.d_moduleSig_134
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ᵈᴵ
d_'10214'_'10215''7496''7477'_792 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_'10214'_'10215''7496''7477'_792 ~v0 v1 v2 v3
  = du_'10214'_'10215''7496''7477'_792 v1 v2 v3
du_'10214'_'10215''7496''7477'_792 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_'10214'_'10215''7496''7477'_792 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceTr.du_trT'8734'_122
      (coe
         MAlonzo.Code.Once.Lang.Trace.C_interp_192
         (coe du_sigOfT_786 (coe v1)) (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.Lang.Core.Telescope.d_runCore_146
         (coe MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedSig_24 (coe v1))
         (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
         (coe
            MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedProgram_52 (coe v1))
         (coe v2))
-- Once.Adequacy.Compile.WithCPU.ir-core-tr
d_ir'45'core'45'tr_808 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_ir'45'core'45'tr_808 ~v0 v1 v2 v3 ~v4 ~v5
  = du_ir'45'core'45'tr_808 v1 v2 v3
du_ir'45'core'45'tr_808 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_ir'45'core'45'tr_808 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Adequacy.CoreBridge.du_program'45'core'45'tr_196
                    (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                    (coe v3) (coe v5) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.exec
d_exec_832 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_exec_832 ~v0 v1 v2 v3 = du_exec_832 v1 v2 v3
du_exec_832 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_exec_832 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_72
      (coe MAlonzo.Code.Once.Adequacy.CPU.d_arch'45'semantics_6 (coe v1))
      (coe v0) (coe v2)
-- Once.Adequacy.Compile.WithCPU._.file-correct
d_file'45'correct_846 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_file'45'correct_846 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_file'45'correct_846 v0 v1 v2 v3 v4 v5
du_file'45'correct_846 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_file'45'correct_846 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Metatheory.Trace.du_WB'45'trans_258 erased
      (coe d_file'45'tr_136 (coe v0 v1 v2) v3 v4 erased v5 erased erased)
      (coe
         MAlonzo.Code.Once.Adequacy.RewritePreserves.d_rewrite'45'program'45'trace_626
         (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v2))
         (coe v1) (coe du_P_866 (coe v3) (coe v5)))
-- Once.Adequacy.Compile.WithCPU._._.P
d_P_866 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_P_866 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 = du_P_866 v3 v5
du_P_866 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
du_P_866 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_870 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_'10214'_'10215''8869''45'ir_870 ~v0 v1 v2 v3
  = du_'10214'_'10215''8869''45'ir_870 v1 v2 v3
du_'10214'_'10215''8869''45'ir_870 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_'10214'_'10215''8869''45'ir_870 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR'7511'_242
                (coe v1)
                (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v2))
                (coe v0))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-adm
d_'10214'_'10215''8869''45'adm_880 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_'10214'_'10215''8869''45'adm_880 ~v0 v1 v2 v3 v4
  = du_'10214'_'10215''8869''45'adm_880 v1 v2 v3 v4
du_'10214'_'10215''8869''45'adm_880 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_'10214'_'10215''8869''45'adm_880 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_'10214'_'10215''8869''45'ir_870 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Compile.d_programAt_1088
                          (coe MAlonzo.Code.Once.Compile.d_moduleTable_1084 (coe v1))
                          (coe MAlonzo.Code.Once.Compile.d_moduleToIR_1052 (coe v1)))
                       (coe v2))
             else coe
                    seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_890 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_'10214'_'10215''8869''45'm_890 ~v0 v1 v2 v3
  = du_'10214'_'10215''8869''45'm_890 v1 v2 v3
du_'10214'_'10215''8869''45'm_890 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_'10214'_'10215''8869''45'm_890 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_'10214'_'10215''8869''45'adm_880 (coe v0) (coe v3) (coe v2)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥
d_'10214'_'10215''8869'_896 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_'10214'_'10215''8869'_896 ~v0 v1 v2 v3
  = du_'10214'_'10215''8869'_896 v1 v2 v3
du_'10214'_'10215''8869'_896 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18
du_'10214'_'10215''8869'_896 v0 v1 v2
  = coe
      du_'10214'_'10215''8869''45'm_890 (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_262 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_912 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_912 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                          ~v6
  = du_'10214''10215''8869''45'ir'45'sound_912 v3
du_'10214''10215''8869''45'ir'45'sound_912 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'ir'45'sound_912 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-adm-sound
d_'10214''10215''8869''45'adm'45'sound_938 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'10214''10215''8869''45'adm'45'sound_938 ~v0 ~v1 v2 ~v3 v4 ~v5
                                           ~v6
  = du_'10214''10215''8869''45'adm'45'sound_938 v2 v4
du_'10214''10215''8869''45'adm'45'sound_938 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_'10214''10215''8869''45'adm'45'sound_938 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_620
                   (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_962 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_962 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'10214''10215''8869''45'm'45'sound_962 v2 v3
du_'10214''10215''8869''45'm'45'sound_962 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'm'45'sound_962 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   du_'10214''10215''8869''45'adm'45'sound_938 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                      (coe v1) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_984 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_984 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'10214''10215''8869''45'sound_984 v2 v3
du_'10214''10215''8869''45'sound_984 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'sound_984 v0 v1
  = coe
      du_'10214''10215''8869''45'm'45'sound_962
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_262 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU._.opt-trace
d_opt'45'trace_1002
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.Compile.WithCPU._.opt-trace"
-- Once.Adequacy.Compile.WithCPU._.TraceAt
d_TraceAt_1004 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_1004 = erased
-- Once.Adequacy.Compile.WithCPU._.correct-fe
d_correct'45'fe_1026 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'fe_1026 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 v10
  = du_correct'45'fe_1026 v6 v8 v10
du_correct'45'fe_1026 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'fe_1026 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_just_40
             (coe v2 v3 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-mir
d_correct'45'mir_1074 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_1074 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8
  = du_correct'45'mir_1074 v2 v3 v4 v5 v8
du_correct'45'mir_1074 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'mir_1074 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_correct'45'fe_1026
             (coe
                MAlonzo.Code.Once.Compile.d_compileFileFromModule_1490
                (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v1) (coe v0) (coe v2))
             erased (coe v4 v5 erased)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-gm
d_correct'45'gm_1112 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm_1112 ~v0 ~v1 v2 v3 v4 v5
  = du_correct'45'gm_1112 v2 v3 v4 v5
du_correct'45'gm_1112 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm_1112 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_correct'45'gm'45'adm_1124 (coe v0) (coe v1) (coe v4)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v0) (coe v4))
             (coe v3 v4 erased)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-gm-adm
d_correct'45'gm'45'adm_1124 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm'45'adm_1124 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_correct'45'gm'45'adm_1124 v2 v3 v4 v5 v6
du_correct'45'gm'45'adm_1124 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm'45'adm_1124 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_correct'45'mir_1074 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.Compile.d_moduleToIR_1052 (coe v2))
                       (coe v4))
             else coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct
d_correct_1180 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_1180 v0 v1 v2 v3 v4 ~v5 = du_correct_1180 v0 v1 v2 v3 v4
du_correct_1180 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_1180 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_correct'45'gm_1112 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_262 (coe v4))
             (coe
                (\ v5 v6 v7 v8 v9 v10 ->
                   coe d_opt'45'trace_1002 v0 v1 v2 v5 v9 v7 erased erased erased))
      else coe
             du_correct'45'gm_1112 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_262 (coe v4))
             (coe
                (\ v5 v6 v7 v8 v9 v10 ->
                   coe
                     du_file'45'correct_846 (coe v0) (coe v1) (coe v2) (coe v5) (coe v9)
                     (coe v7)))
-- Once.Adequacy.Compile.WithCPU._.pw-just-inv
d_pw'45'just'45'inv_1224 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_1224 ~v0 ~v1 ~v2 v3 ~v4
  = du_pw'45'just'45'inv_1224 v3
du_pw'45'just'45'inv_1224 ::
  Maybe MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pw'45'just'45'inv_1224 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.pw-just-rel
d_pw'45'just'45'rel_1232 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_pw'45'just'45'rel_1232 ~v0 ~v1 ~v2 ~v3 v4
  = du_pw'45'just'45'rel_1232 v4
du_pw'45'just'45'rel_1232 ::
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_pw'45'just'45'rel_1232 v0
  = case coe v0 of
      MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_just_40 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-just-adm
d_'10214''10215''8869''45'just'45'adm_1242 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just'45'adm_1242 = erased
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-just
d_'10214''10215''8869''45'just_1266 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_1266 = erased
-- Once.Adequacy.Compile.WithCPU._._.go
d_go_1288 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1288 = erased
-- Once.Adequacy.Compile.WithCPU._.sound-trace
d_sound'45'trace_1318 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_sound'45'trace_1318 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_sound'45'trace_1318 v0 v1 v2 v3 v4
du_sound'45'trace_1318 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_sound'45'trace_1318 v0 v1 v2 v3 v4
  = coe du_e'8779'_1362 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.WithCPU._._.ls′
d_ls'8242'_1346 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ls'8242'_1346 = erased
-- Once.Adequacy.Compile.WithCPU._._.p
d_p_1352 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_p_1352 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_p_1352 v0 v1 v2 v3 v4
du_p_1352 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_p_1352 v0 v1 v2 v3 v4
  = coe du_correct_1180 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.WithCPU._._.admR
d_admR_1356 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_admR_1356 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_admR_1356 v2 v7
du_admR_1356 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_admR_1356 v0 v1 = coe du_accept'45'gm_462 (coe v0) (coe v1)
-- Once.Adequacy.Compile.WithCPU._._.p'
d_p''_1358 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_p''_1358 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_p''_1358 v0 v1 v2 v3 v4
du_p''_1358 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_p''_1358 v0 v1 v2 v3 v4
  = coe du_p_1352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.WithCPU._._.e≋
d_e'8779'_1362 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
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
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_e'8779'_1362 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_e'8779'_1362 v0 v1 v2 v3 v4
du_e'8779'_1362 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_e'8779'_1362 v0 v1 v2 v3 v4
  = coe
      du_pw'45'just'45'rel_1232
      (coe du_p''_1358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.Compile.WithCPU.correctᵈ
d_correct'7496'_1380 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_1380 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v4 v5 -> coe du_sound_1398 (coe v0) (coe v1) (coe v2) (coe v3))
      (\ v4 v5 v6 ->
         coe du_correctR'45'complete_566 (coe v1) (coe v2) v4 v5)
-- Once.Adequacy.Compile.WithCPU._.sound
d_sound_1398 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sound_1398 v0 v1 v2 v3 ~v4 ~v5 = du_sound_1398 v0 v1 v2 v3
du_sound_1398 ::
  (MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_96) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sound_1398 v0 v1 v2 v3
  = let v4
          = coe
              du_accept'45'typed'45'aux_720
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_254
                 (coe
                    MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50 (coe v3))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_250
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
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v3)))
                                   (coe (0 :: Integer)))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                            (coe v3)))
                                      (coe (0 :: Integer))))
                                (\ v4 v5 v6 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                              (coe v3)))
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
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v3)))
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
                                            (coe v3)))
                                      (coe (0 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                      (coe
                                         MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                            (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                               (coe v3)))
                                         (coe (0 :: Integer))))
                                   (\ v4 v5 v6 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                        (coe
                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                 (coe v3)))
                                           (coe (0 :: Integer)))))))))))
              erased in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> let v9
                           = MAlonzo.Code.Once.Compile.d_moduleToIR'45'aux_1048
                               (coe
                                  MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_830
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                  (coe
                                     MAlonzo.Code.Once.Parser.d_guardDistinct_538
                                     (coe
                                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v5))
                                        (coe
                                           MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v5))
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                            -> let v11
                                     = coe
                                         MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_314
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
                                                              (coe v3)))
                                                        (coe (0 :: Integer)))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                 (coe v3)))
                                                           (coe (0 :: Integer))))
                                                     (\ v11 v12 v13 ->
                                                        coe
                                                          MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                   (coe v3)))
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
                                                              (coe v3)))
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
                                                                 (coe v3)))
                                                           (coe (0 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                 (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                    (coe v3)))
                                                              (coe (0 :: Integer))))
                                                        (\ v11 v12 v13 ->
                                                           coe
                                                             MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                      (coe v3)))
                                                                (coe (0 :: Integer))))))))) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                      -> coe
                                           seq (coe v13)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v5)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_820
                                                       (coe v5) (coe v8) (coe v10))))
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
                                                             (coe v3)))
                                                       (coe
                                                          MAlonzo.Code.Once.Adequacy.ResolveBridge.du_resolvesModule'45'complete_2092
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50
                                                             (coe v3))
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                             (coe v12)))))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe du_accept'45'gm_462 (coe v1) (coe v5))
                                                    (coe
                                                       (\ v14 ->
                                                          coe
                                                            MAlonzo.Code.Once.Metatheory.Trace.du_WB'45'trans_258
                                                            erased
                                                            (coe
                                                               du_sound'45'trace_1318 (coe v0)
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Trace.C_interp_192
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Module.d_moduleSig_134
                                                                     (coe v5))
                                                                  (coe v14))
                                                               (coe v1) (coe v2) (coe v3))
                                                            (coe
                                                               du_ir'45'core'45'tr_808 (coe v1)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v5)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe v8)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_820
                                                                        (coe v5) (coe v8)
                                                                        (coe v10))))
                                                               (coe v14)))))))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> let v10 = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12 in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                      -> let v13
                                               = coe
                                                   MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_314
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
                                                                        (coe v3)))
                                                                  (coe (0 :: Integer)))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                           (coe v3)))
                                                                     (coe (0 :: Integer))))
                                                               (\ v13 v14 v15 ->
                                                                  coe
                                                                    MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                          (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                             (coe v3)))
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
                                                                        (coe v3)))
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
                                                                           (coe v3)))
                                                                     (coe (0 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                              (coe v3)))
                                                                        (coe (0 :: Integer))))
                                                                  (\ v13 v14 v15 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_616
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                             (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                                (coe v3)))
                                                                          (coe
                                                                             (0 ::
                                                                                Integer))))))))) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                -> coe
                                                     seq (coe v15)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v5)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v8)
                                                              (coe
                                                                 MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_820
                                                                 (coe v5) (coe v8) (coe v11))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v14)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.FrontEndBridge.du_parseStrict'45'sound_448
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52
                                                                       (coe v3)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.ResolveBridge.du_resolvesModule'45'complete_2092
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50
                                                                       (coe v3))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                                       (coe v14)))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 du_accept'45'gm_462 (coe v1)
                                                                 (coe v5))
                                                              (coe
                                                                 (\ v16 ->
                                                                    coe
                                                                      MAlonzo.Code.Once.Metatheory.Trace.du_WB'45'trans_258
                                                                      erased
                                                                      (coe
                                                                         du_sound'45'trace_1318
                                                                         (coe v0)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Lang.Trace.C_interp_192
                                                                            (coe
                                                                               MAlonzo.Code.Once.Lang.Module.d_moduleSig_134
                                                                               (coe v5))
                                                                            (coe v16))
                                                                         (coe v1) (coe v2) (coe v3))
                                                                      (coe
                                                                         du_ir'45'core'45'tr_808
                                                                         (coe v1)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v5)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe v8)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_820
                                                                                  (coe v5) (coe v8)
                                                                                  (coe v11))))
                                                                         (coe v16)))))))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
