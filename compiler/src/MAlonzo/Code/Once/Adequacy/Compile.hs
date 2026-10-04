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
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.Telescope
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Spec.Resolution
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1080
d_compile'45'asm_6 v0 v1
  = let v2
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_382
              (coe
                 MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_202 (coe v1))
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_378
                 (coe
                    MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204 (coe v1)))
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                         (coe v1)))
                                   (coe (0 :: Integer))))
                             (\ v2 v3 v4 ->
                                coe
                                  MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                  (coe
                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                           (coe v1)))
                                     (coe (0 :: Integer)))))))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Parser.Module.d_r_370
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                (coe
                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204 (coe v1)))
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
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                         (coe v1)))
                                   (coe (0 :: Integer)))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                            (coe v1)))
                                      (coe (0 :: Integer))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                              (coe v1)))
                                        (coe (0 :: Integer)))))))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1306
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_1078)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Once.Compile.C_Error_1088
                (coe
                   ("front-end (parse / import resolution) failed" :: Data.Text.Text))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.compile-cli-asm
d_compile'45'cli'45'asm_26 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Compile.T_Stage_1072 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1080
d_compile'45'cli'45'asm_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_1306 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.⟦_⟧M
d_'10214'_'10215'M_38 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215'M_38 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_362
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToProgram_98
         (coe v0))
      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.ArchCorrect
d_ArchCorrect_52 a0 a1 a2 = ()
data T_ArchCorrect_52
  = C_constructor_136 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6)
                      (MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                       MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6)
-- Once.Adequacy.Compile.ArchCorrect.asm-sem
d_asm'45'sem_98 ::
  T_ArchCorrect_52 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_asm'45'sem_98 v0
  = case coe v0 of
      C_constructor_136 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.flat-trace
d_flat'45'trace_102 ::
  T_ArchCorrect_52 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_flat'45'trace_102 v0
  = case coe v0 of
      C_constructor_136 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.assemble-correct
d_assemble'45'correct_110 ::
  T_ArchCorrect_52 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assemble'45'correct_110 = erased
-- Once.Adequacy.Compile.ArchCorrect.asm-trace-correct
d_asm'45'trace'45'correct_126 ::
  T_ArchCorrect_52 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct_126 = erased
-- Once.Adequacy.Compile.ArchCorrect.ir-flat-correct
d_ir'45'flat'45'correct_134 ::
  T_ArchCorrect_52 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct_134 = erased
-- Once.Adequacy.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_148 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gmoduleToModule'45'correct_148 = erased
-- Once.Adequacy.Compile.WithCPU.string-to-bytes
d_string'45'to'45'bytes_174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_174 v0 ~v1 v2
  = du_string'45'to'45'bytes_174 v0 v2
du_string'45'to'45'bytes_174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_string'45'to'45'bytes_174 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 (coe v0 v1)
-- Once.Adequacy.Compile.WithCPU.compile-cr
d_compile'45'cr_178 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1080 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_178 v0 ~v1 v2 v3 = du_compile'45'cr_178 v0 v2 v3
du_compile'45'cr_178 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1080 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'cr_178 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Compile.C_Parsed_1082 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Checked_1084 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Built_1086 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_string'45'to'45'bytes_174 v0 v1 v3)
      MAlonzo.Code.Once.Compile.C_Error_1088 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-mir
d_compile'45'mir_190 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_190 v0 ~v1 v2 v3 v4 v5
  = du_compile'45'mir_190 v0 v2 v3 v4 v5
du_compile'45'mir_190 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_190 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_compile'45'cr_178 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1306
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_1078) (coe v2) (coe v1)
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-gm
d_compile'45'gm_204 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_204 v0 ~v1 v2 v3 v4
  = du_compile'45'gm_204 v0 v2 v3 v4
du_compile'45'gm_204 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_204 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_compile'45'mir_190 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_54 (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile
d_compile_216 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_216 v0 ~v1 v2 v3 v4 = du_compile_216 v0 v2 v3 v4
du_compile_216 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_216 v0 v1 v2 v3
  = coe
      du_compile'45'gm_204 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_390 (coe v3))
-- Once.Adequacy.Compile.WithCPU.refuse-gated
d_refuse'45'gated_234 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gated_234 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-ef
d_refuse'45'ef_266 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'ef_266 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-mir
d_refuse'45'mir_296 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'mir_296 = erased
-- Once.Adequacy.Compile.WithCPU.refuse-gm
d_refuse'45'gm_322 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refuse'45'gm_322 = erased
-- Once.Adequacy.Compile.WithCPU.accept-gated
d_accept'45'gated_344 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gated_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_accept'45'gated_344 v6
du_accept'45'gated_344 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gated_344 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.accept-ef
d_accept'45'ef_376 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'ef_376 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7
  = du_accept'45'ef_376 v2 v4 v5
du_accept'45'ef_376 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'ef_376 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'gated_344
         (coe
            MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
            (coe v0) (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-mir
d_accept'45'mir_406 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'mir_406 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7
  = du_accept'45'mir_406 v2 v4 v5
du_accept'45'mir_406 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'mir_406 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_accept'45'ef_376 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Parser.d_extractFunctions_572
            (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
            (coe v1)))
-- Once.Adequacy.Compile.WithCPU.accept-gm
d_accept'45'gm_432 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_accept'45'gm_432 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6
  = du_accept'45'gm_432 v2 v4
du_accept'45'gm_432 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_accept'45'gm_432 v0 v1
  = coe
      du_accept'45'mir_406 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_54 (coe v1))
-- Once.Adequacy.Compile.WithCPU._≋_
d__'8779'__442 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 -> ()
d__'8779'__442 = erased
-- Once.Adequacy.Compile.WithCPU.compile-just-ir
d_compile'45'just'45'ir_462 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'just'45'ir_462 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_compile'45'just'45'ir_462 v5
du_compile'45'just'45'ir_462 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'just'45'ir_462 v0
  = let v1
          = MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR'45'aux_50
              (coe
                 MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_700
                 (coe MAlonzo.Code.Once.IR.C_Heap_8)
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                 (coe
                    MAlonzo.Code.Once.Parser.d_guardDistinct_560
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
d_c'8801'n_518 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_518 = erased
-- Once.Adequacy.Compile.WithCPU.correctR-complete
d_correctR'45'complete_538 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correctR'45'complete_538 v0 ~v1 v2 v3 ~v4 v5 v6 ~v7
  = du_correctR'45'complete_538 v0 v2 v3 v5 v6
du_correctR'45'complete_538 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correctR'45'complete_538 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           seq (coe v10)
                           (let v11
                                  = let v11
                                          = MAlonzo.Code.Once.Parser.d_guardDistinct_560
                                              (coe
                                                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                    (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                    (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
                                    coe
                                      (case coe v11 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                           -> let v13
                                                    = MAlonzo.Code.Once.Adequacy.ModuleComplete.d_ce'45'find'45'complete_322
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_emptyCScope_388)
                                                        (coe v12) (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe v8))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe v8)) in
                                              coe
                                                (case coe v13 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                     -> case coe v15 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                            -> coe
                                                                 seq (coe v17)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v16) erased)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError) in
                            coe
                              (coe
                                 seq (coe v11)
                                 (let v12
                                        = coe
                                            MAlonzo.Code.Once.Adequacy.MainBuilds.du_cfm'45'built'45'aux_598
                                            (coe v1) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_guardDistinct_560
                                               (coe
                                                  MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.d_extractAliases_76
                                                     (coe v5))
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                     (coe v5))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Once.Adequacy.MainBuilds.du_crm'45'doOpt_536
                                                  (coe v2) (coe v5)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Once.Adequacy.MainBuilds.du_moduleToIR'45'inj'8322'_662
                                                        (coe v5))))) in
                                  coe
                                    (case coe v12 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe du_string'45'to'45'bytes_174 v0 v1 v13) erased
                                       _ -> MAlonzo.RTE.mazUnreachableError))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.p-eq
d_p'45'eq_624 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'45'eq_624 = erased
-- Once.Adequacy.Compile.WithCPU._.res-eq
d_res'45'eq_626 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_res'45'eq_626 = erased
-- Once.Adequacy.Compile.WithCPU._.stm-eq
d_stm'45'eq_628 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stm'45'eq_628 = erased
-- Once.Adequacy.Compile.WithCPU._.c≡j
d_c'8801'j_630 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_406 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'j_630 = erased
-- Once.Adequacy.Compile.WithCPU.accept-typed-aux
d_accept'45'typed'45'aux_656 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'typed'45'aux_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8
  = du_accept'45'typed'45'aux_656 v6 v7
du_accept'45'typed'45'aux_656 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'typed'45'aux_656 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_606
                   (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.c≡n
d_c'8801'n_674 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8801'n_674 = erased
-- Once.Adequacy.Compile.WithCPU.accept-typed
d_accept'45'typed_704 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'typed_704 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_accept'45'typed_704 v4
du_accept'45'typed_704 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'typed_704 v0
  = coe
      du_accept'45'typed'45'aux_656
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_390 (coe v0))
      erased
-- Once.Adequacy.Compile.WithCPU.Admissible
d_Admissible_716 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Admissible_716 = erased
-- Once.Adequacy.Compile.WithCPU.sigOfT
d_sigOfT_722 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigOfT_722 ~v0 ~v1 v2 = du_sigOfT_722 v2
du_sigOfT_722 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_sigOfT_722 v0
  = coe
      MAlonzo.Code.Once.Spec.Module.d_moduleSig_160
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
-- Once.Adequacy.Compile.WithCPU.core-run
d_core'45'run_732 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_core'45'run_732 ~v0 ~v1 v2 v3 v4 = du_core'45'run_732 v2 v3 v4
du_core'45'run_732 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_core'45'run_732 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.d_runProgram_146
      (coe MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedSig_24 (coe v1))
      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.CoreBridge.du_typedProgram_52 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.WithCPU.ir-core
d_ir'45'core_750 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'core_750 = erased
-- Once.Adequacy.Compile.WithCPU.⟦_⟧ᵈᴵ
d_'10214'_'10215''7496''7477'_772 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''7496''7477'_772 ~v0 ~v1 v2 v3 v4
  = du_'10214'_'10215''7496''7477'_772 v2 v3 v4
du_'10214'_'10215''7496''7477'_772 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''7496''7477'_772 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.du_behavior'45'by_50
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_362
         (coe
            MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToProgram_98
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
         (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v0))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_468
            (coe du_sigOfT_722 (coe v1)) (coe v2)))
      (coe du_core'45'run_732 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.Compile.WithCPU._.ir
d_ir_784 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ir_784 ~v0 ~v1 ~v2 v3 ~v4 = du_ir_784 v3
du_ir_784 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ir_784 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.Adequacy.ModuleComplete.d_moduleToIR'45'complete_506
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))))
-- Once.Adequacy.Compile.WithCPU._.mi
d_mi_786 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mi_786 = erased
-- Once.Adequacy.Compile.WithCPU._.exec
d_exec_794 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_exec_794 v0 ~v1 v2 v3 v4 = du_exec_794 v0 v2 v3 v4
du_exec_794 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_exec_794 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0 v2) (coe v1) (coe v3)
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧A_
d_'10214'_'10215'A__800 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215'A__800 ~v0 v1 v2 v3 v4
  = du_'10214'_'10215'A__800 v1 v2 v3 v4
du_'10214'_'10215'A__800 ::
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215'A__800 v0 v1 v2 v3
  = coe d_asm'45'sem_98 (coe v0 v1 v2) v3
-- Once.Adequacy.Compile.WithCPU._.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_814 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_814 = erased
-- Once.Adequacy.Compile.WithCPU._.codegen-asm-correct
d_codegen'45'asm'45'correct_836 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_836 = erased
-- Once.Adequacy.Compile.WithCPU._._.P
d_P_858 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_P_858 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 = du_P_858 v4 v6
du_P_858 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_P_858 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleTable_86 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU._.module-to-asm-correct
d_module'45'to'45'asm'45'correct_872 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_872 = erased
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_890 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869''45'ir_890 ~v0 ~v1 v2 v3 v4
  = du_'10214'_'10215''8869''45'ir_890 v2 v3 v4
du_'10214'_'10215''8869''45'ir_890 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869''45'ir_890 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_362
                (coe v1)
                (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_78 (coe v2))
                (coe v0))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-adm
d_'10214'_'10215''8869''45'adm_900 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869''45'adm_900 ~v0 ~v1 v2 v3 v4 v5
  = du_'10214'_'10215''8869''45'adm_900 v2 v3 v4 v5
du_'10214'_'10215''8869''45'adm_900 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869''45'adm_900 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_'10214'_'10215''8869''45'ir_890 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Adequacy.SourceTrace.d_programAt_90
                          (coe
                             MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleTable_86 (coe v1))
                          (coe
                             MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_54 (coe v1)))
                       (coe v2))
             else coe
                    seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_910 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869''45'm_910 ~v0 ~v1 v2 v3 v4
  = du_'10214'_'10215''8869''45'm_910 v2 v3 v4
du_'10214'_'10215''8869''45'm_910 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869''45'm_910 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_'10214'_'10215''8869''45'adm_900 (coe v0) (coe v3) (coe v2)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦_⟧⊥
d_'10214'_'10215''8869'_916 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_'10214'_'10215''8869'_916 ~v0 ~v1 v2 v3 v4
  = du_'10214'_'10215''8869'_916 v2 v3 v4
du_'10214'_'10215''8869'_916 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
du_'10214'_'10215''8869'_916 v0 v1 v2
  = coe
      du_'10214'_'10215''8869''45'm_910 (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_390 (coe v1))
      (coe v2)
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-ir-sound
d_'10214''10215''8869''45'ir'45'sound_932 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'ir'45'sound_932 ~v0 ~v1 ~v2 ~v3 v4 ~v5
                                          ~v6 ~v7
  = du_'10214''10215''8869''45'ir'45'sound_932 v4
du_'10214''10215''8869''45'ir'45'sound_932 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'ir'45'sound_932 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-adm-sound
d_'10214''10215''8869''45'adm'45'sound_958 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'10214''10215''8869''45'adm'45'sound_958 ~v0 ~v1 ~v2 v3 ~v4 v5
                                           ~v6 ~v7
  = du_'10214''10215''8869''45'adm'45'sound_958 v3 v5
du_'10214''10215''8869''45'adm'45'sound_958 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> AgdaAny
du_'10214''10215''8869''45'adm'45'sound_958 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_606
                   (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-m-sound
d_'10214''10215''8869''45'm'45'sound_982 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'm'45'sound_982 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_'10214''10215''8869''45'm'45'sound_982 v3 v4
du_'10214''10215''8869''45'm'45'sound_982 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'm'45'sound_982 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   du_'10214''10215''8869''45'adm'45'sound_958 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                      (coe v1) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-sound
d_'10214''10215''8869''45'sound_1004 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214''10215''8869''45'sound_1004 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_'10214''10215''8869''45'sound_1004 v3 v4
du_'10214''10215''8869''45'sound_1004 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214''10215''8869''45'sound_1004 v0 v1
  = coe
      du_'10214''10215''8869''45'm'45'sound_982
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_390 (coe v0))
      (coe v1)
-- Once.Adequacy.Compile.WithCPU._.opt-trace
d_opt'45'trace_1024
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.Compile.WithCPU._.opt-trace"
-- Once.Adequacy.Compile.WithCPU._.TraceAt
d_TraceAt_1026 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_1026 = erased
-- Once.Adequacy.Compile.WithCPU._.correct-cr
d_correct'45'cr_1048 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_1080 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_1048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 ~v10 v11
  = du_correct'45'cr_1048 v7 v9 v11
du_correct'45'cr_1048 ::
  MAlonzo.Code.Once.Compile.T_CompileResult_1080 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'cr_1048 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Compile.C_Parsed_1082 v3 v4 -> erased
      MAlonzo.Code.Once.Compile.C_Checked_1084 v3 -> erased
      MAlonzo.Code.Once.Compile.C_Built_1086 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_just_40
             (coe v2 v3 v1)
      MAlonzo.Code.Once.Compile.C_Error_1088 v3 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-mir
d_correct'45'mir_1126 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'mir_1126 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
  = du_correct'45'mir_1126 v3 v4 v5 v6
du_correct'45'mir_1126 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'mir_1126 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_correct'45'cr_1048
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_1306
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_1078) (coe v1) (coe v0)
                (coe v2))
             erased erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-gm
d_correct'45'gm_1164 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm_1164 ~v0 ~v1 ~v2 v3 v4 v5 ~v6
  = du_correct'45'gm_1164 v3 v4 v5
du_correct'45'gm_1164 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm_1164 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_correct'45'gm'45'adm_1176 (coe v0) (coe v1) (coe v3)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v0) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct-gm-adm
d_correct'45'gm'45'adm_1176 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Once.IR.T_IR_16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'gm'45'adm_1176 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7
  = du_correct'45'gm'45'adm_1176 v3 v4 v5 v6
du_correct'45'gm'45'adm_1176 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm'45'adm_1176 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       du_correct'45'mir_1126 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_54 (coe v2)))
             else coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.correct
d_correct_1232 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  (MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_1232 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 = du_correct_1232 v3 v4 v5
du_correct_1232 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_1232 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         du_correct'45'gm_1164 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule_390 (coe v2)))
-- Once.Adequacy.Compile.WithCPU._.pw-just-inv
d_pw'45'just'45'inv_1280 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pw'45'just'45'inv_1280 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_pw'45'just'45'inv_1280 v4
du_pw'45'just'45'inv_1280 ::
  Maybe MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pw'45'just'45'inv_1280 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU._.pw-just-rel
d_pw'45'just'45'rel_1288 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45'just'45'rel_1288 = erased
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-just-adm
d_'10214''10215''8869''45'just'45'adm_1298 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just'45'adm_1298 = erased
-- Once.Adequacy.Compile.WithCPU._.⟦⟧⊥-just
d_'10214''10215''8869''45'just_1322 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10214''10215''8869''45'just_1322 = erased
-- Once.Adequacy.Compile.WithCPU._._.go
d_go_1344 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1344 = erased
-- Once.Adequacy.Compile.WithCPU._.sound-trace
d_sound'45'trace_1374 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sound'45'trace_1374 = erased
-- Once.Adequacy.Compile.WithCPU._._.ls′
d_ls'8242'_1404 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
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
d_ls'8242'_1404 = erased
-- Once.Adequacy.Compile.WithCPU._._.p
d_p_1410 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_p_1410 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_p_1410 v3 v4 v5
du_p_1410 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_p_1410 v0 v1 v2 = coe du_correct_1232 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU._._.admR
d_admR_1414 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_admR_1414 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
            ~v13
  = du_admR_1414 v3 v8
du_admR_1414 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_admR_1414 v0 v1 = coe du_accept'45'gm_432 (coe v0) (coe v1)
-- Once.Adequacy.Compile.WithCPU._._.p'
d_p''_1416 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_p''_1416 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_p''_1416 v3 v4 v5
du_p''_1416 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_p''_1416 v0 v1 v2 = coe du_p_1410 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU._._.e≋
d_e'8779'_1420 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e'8779'_1420 = erased
-- Once.Adequacy.Compile.WithCPU.correctᵈ
d_correct'7496'_1438 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_correct'7496'_1438 v0 ~v1 v2 v3 v4
  = du_correct'7496'_1438 v0 v2 v3 v4
du_correct'7496'_1438 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_correct'7496'_1438 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v4 v5 -> coe du_sound_1456 (coe v1) (coe v3))
      (\ v4 v5 v6 ->
         coe du_correctR'45'complete_538 (coe v0) (coe v1) (coe v2) v4 v5)
-- Once.Adequacy.Compile.WithCPU._.sound
d_sound_1456 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
   MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_52) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sound_1456 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 = du_sound_1456 v2 v4
du_sound_1456 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_196 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sound_1456 v0 v1
  = let v2
          = coe
              du_accept'45'typed'45'aux_656
              (coe
                 MAlonzo.Code.Once.Adequacy.SourceTrace.d_srcToModule'45'aux_382
                 (coe
                    MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_202 (coe v1))
                 (coe
                    MAlonzo.Code.Once.Adequacy.SourceTrace.d_eitherToMaybe_378
                    (coe
                       MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                         (coe v1)))
                                   (coe (0 :: Integer)))
                                (coe
                                   MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                   (coe
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                            (coe v1)))
                                      (coe (0 :: Integer))))
                                (\ v2 v3 v4 ->
                                   coe
                                     MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                     (coe
                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                              (coe v1)))
                                        (coe (0 :: Integer)))))))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Parser.Module.d_r_370
                                (coe
                                   MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                      (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
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
                                      MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                         (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                            (coe v1)))
                                      (coe (0 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                      (coe
                                         MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                            (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                               (coe v1)))
                                         (coe (0 :: Integer))))
                                   (\ v2 v3 v4 ->
                                      coe
                                        MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                        (coe
                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                 (coe v1)))
                                           (coe (0 :: Integer)))))))))))
              erased in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> let v7
                           = MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR'45'aux_50
                               (coe
                                  MAlonzo.Code.Once.Compile.du_compileResolvedModule'45'aux_700
                                  (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                  (coe
                                     MAlonzo.Code.Once.Parser.d_guardDistinct_560
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
                                         MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_442
                                         (coe
                                            MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                              (coe v1)))
                                                        (coe (0 :: Integer)))
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                 (coe v1)))
                                                           (coe (0 :: Integer))))
                                                     (\ v9 v10 v11 ->
                                                        coe
                                                          MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                   (coe v1)))
                                                             (coe (0 :: Integer)))))))
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.Module.d_r_370
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
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
                                                           MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                 (coe v1)))
                                                           (coe (0 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                 (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                    (coe v1)))
                                                              (coe (0 :: Integer))))
                                                        (\ v9 v10 v11 ->
                                                           coe
                                                             MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                   (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
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
                                                       MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_810
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
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                             (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Once.Adequacy.ResolveBridge.du_resolvesModule'45'complete_2268
                                                          (coe
                                                             MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_202
                                                             (coe v1))
                                                          (coe
                                                             MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                             (coe v10)))))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe du_accept'45'gm_432 (coe v0) (coe v3))
                                                    erased)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> let v8 = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12 in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                      -> let v11
                                               = coe
                                                   MAlonzo.Code.Once.Adequacy.SourceTrace.du_srcToModule'45'inv'45'p_442
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                        (coe v1)))
                                                                  (coe (0 :: Integer)))
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                           (coe v1)))
                                                                     (coe (0 :: Integer))))
                                                               (\ v11 v12 v13 ->
                                                                  coe
                                                                    MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                          (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                             (coe v1)))
                                                                       (coe (0 :: Integer)))))))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.Module.d_r_370
                                                               (coe
                                                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                     (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
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
                                                                     MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                        (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                           (coe v1)))
                                                                     (coe (0 :: Integer)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                                                                     (coe
                                                                        MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                           (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                              (coe v1)))
                                                                        (coe (0 :: Integer))))
                                                                  (\ v11 v12 v13 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                             (MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
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
                                                                 MAlonzo.Code.Once.Adequacy.ModuleComplete.du_moduleToIR'45'sound_810
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
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcText_204
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Adequacy.ResolveBridge.du_resolvesModule'45'complete_2268
                                                                    (coe
                                                                       MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_202
                                                                       (coe v1))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Parser.Module.Core.d_decls_36
                                                                       (coe v12)))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 du_accept'45'gm_432 (coe v0)
                                                                 (coe v3))
                                                              erased)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
