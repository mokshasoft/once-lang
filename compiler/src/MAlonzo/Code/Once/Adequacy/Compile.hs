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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Once.Adequacy.CPU.Interface
import qualified MAlonzo.Code.Once.Adequacy.SourceTrace
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ModuleConvert
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.Compile.compile-asm
d_compile'45'asm_6 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636
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
                   MAlonzo.Code.Once.Compile.d_compileFromModule_832
                   (coe MAlonzo.Code.Once.IR.C_Heap_8)
                   (coe MAlonzo.Code.Once.Compile.C_Build_634)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v4))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Once.Compile.d_compileFromModule_832
                       (coe MAlonzo.Code.Once.IR.C_Heap_8)
                       (coe MAlonzo.Code.Once.Compile.C_Build_634)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Once.Compile.C_Error_644
                       (coe ("GModule \8594 Module conversion failed" :: Data.Text.Text))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.Compile.compile-cli-asm
d_compile'45'cli'45'asm_26 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Compile.T_Stage_628 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636
d_compile'45'cli'45'asm_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_compileFromModule_832 (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4)
-- Once.Adequacy.Compile.⟦_⟧M
d_'10214'_'10215'M_38 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'M_38 v0
  = coe
      MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_44
      (coe
         MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_40 (coe v0))
-- Once.Adequacy.Compile.ArchCorrect
d_ArchCorrect_46 a0 a1 = ()
data T_ArchCorrect_46
  = C_constructor_100 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
                      (Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
                       Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
-- Once.Adequacy.Compile.ArchCorrect.asm-sem
d_asm'45'sem_76 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_asm'45'sem_76 v0
  = case coe v0 of
      C_constructor_100 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.flat-trace
d_flat'45'trace_78 ::
  T_ArchCorrect_46 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_flat'45'trace_78 v0
  = case coe v0 of
      C_constructor_100 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.ArchCorrect.assemble-correct
d_assemble'45'correct_84 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assemble'45'correct_84 = erased
-- Once.Adequacy.Compile.ArchCorrect.asm-trace-correct
d_asm'45'trace'45'correct_92 ::
  T_ArchCorrect_46 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_asm'45'trace'45'correct_92 = erased
-- Once.Adequacy.Compile.ArchCorrect.ir-flat-correct
d_ir'45'flat'45'correct_98 ::
  T_ArchCorrect_46 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'flat'45'correct_98 = erased
-- Once.Adequacy.Compile.gmoduleToModule-correct
d_gmoduleToModule'45'correct_108 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gmoduleToModule'45'correct_108 = erased
-- Once.Adequacy.Compile.WithCPU.exec
d_exec_126 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_exec_126 v0 ~v1 v2 v3 = du_exec_126 v0 v2 v3
du_exec_126 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_exec_126 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_exec'45'bytes_40
      (coe v0 v1) (coe v2)
-- Once.Adequacy.Compile.WithCPU.string-to-bytes
d_string'45'to'45'bytes_132 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_string'45'to'45'bytes_132 v0 ~v1 v2
  = du_string'45'to'45'bytes_132 v0 v2
du_string'45'to'45'bytes_132 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_string'45'to'45'bytes_132 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CPU.Interface.d_assemble_38 (coe v0 v1)
-- Once.Adequacy.Compile.WithCPU.compile-cr
d_compile'45'cr_136 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'cr_136 v0 ~v1 v2 v3 = du_compile'45'cr_136 v0 v2 v3
du_compile'45'cr_136 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'cr_136 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Compile.C_Parsed_638 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Checked_640 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Compile.C_Built_642 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_string'45'to'45'bytes_132 v0 v1 v3)
      MAlonzo.Code.Once.Compile.C_Error_644 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-mir
d_compile'45'mir_148 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'mir_148 v0 ~v1 v2 v3 v4 v5
  = du_compile'45'mir_148 v0 v2 v3 v4 v5
du_compile'45'mir_148 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'mir_148 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_compile'45'cr_136 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_832
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_634) (coe v2) (coe v1)
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile-gm
d_compile'45'gm_162 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile'45'gm_162 v0 ~v1 v2 v3 v4
  = du_compile'45'gm_162 v0 v2 v3 v4
du_compile'45'gm_162 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile'45'gm_162 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_compile'45'mir_148 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_40 (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.compile
d_compile_174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_compile_174 v0 ~v1 v2 v3 v4 = du_compile_174 v0 v2 v3 v4
du_compile_174 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_compile_174 v0 v1 v2 v3
  = coe
      du_compile'45'gm_162 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Grammar.ModuleConvert.d_gmoduleToModule_144
         (coe v3))
-- Once.Adequacy.Compile.WithCPU.⟦_⟧A_
d_'10214'_'10215'A__182 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_'10214'_'10215'A__182 ~v0 v1 v2 v3
  = du_'10214'_'10215'A__182 v1 v2 v3
du_'10214'_'10215'A__182 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_'10214'_'10215'A__182 v0 v1 v2
  = coe d_asm'45'sem_76 (coe v0 v1) v2
-- Once.Adequacy.Compile.WithCPU.string-to-bytes-correct
d_string'45'to'45'bytes'45'correct_194 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_string'45'to'45'bytes'45'correct_194 = erased
-- Once.Adequacy.Compile.WithCPU.codegen-asm-correct
d_codegen'45'asm'45'correct_210 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_codegen'45'asm'45'correct_210 = erased
-- Once.Adequacy.Compile.WithCPU.module-to-asm-correct
d_module'45'to'45'asm'45'correct_230 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'to'45'asm'45'correct_230 = erased
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-ir
d_'10214'_'10215''8869''45'ir_242 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'ir_242 ~v0 ~v1 v2
  = du_'10214'_'10215''8869''45'ir_242 v2
du_'10214'_'10215''8869''45'ir_242 ::
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869''45'ir_242 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_'10214'_'10215'IR_44
                (coe v0))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥-m
d_'10214'_'10215''8869''45'm_246 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869''45'm_246 ~v0 ~v1 v2
  = du_'10214'_'10215''8869''45'm_246 v2
du_'10214'_'10215''8869''45'm_246 ::
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869''45'm_246 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             du_'10214'_'10215''8869''45'ir_242
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_40 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.⟦_⟧⊥
d_'10214'_'10215''8869'_250 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
d_'10214'_'10215''8869'_250 ~v0 ~v1 v2
  = du_'10214'_'10215''8869'_250 v2
du_'10214'_'10215''8869'_250 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe
    (Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122])
du_'10214'_'10215''8869'_250 v0
  = coe
      du_'10214'_'10215''8869''45'm_246
      (coe
         MAlonzo.Code.Once.Grammar.ModuleConvert.d_gmoduleToModule_144
         (coe v0))
-- Once.Adequacy.Compile.WithCPU.opt-trace
d_opt'45'trace_264
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.Compile.WithCPU.opt-trace"
-- Once.Adequacy.Compile.WithCPU._≋_
d__'8779'__266 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]) ->
  ()
d__'8779'__266 = erased
-- Once.Adequacy.Compile.WithCPU.TraceAt
d_TraceAt_274 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_TraceAt_274 = erased
-- Once.Adequacy.Compile.WithCPU.correct-cr
d_correct'45'cr_296 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompileResult_636 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct'45'cr_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 v9
  = du_correct'45'cr_296 v6 v7 v9
du_correct'45'cr_296 ::
  MAlonzo.Code.Once.Compile.T_CompileResult_636 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'cr_296 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Compile.C_Parsed_638 v3 v4 -> erased
      MAlonzo.Code.Once.Compile.C_Checked_640 v3 -> erased
      MAlonzo.Code.Once.Compile.C_Built_642 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_just_40
             (coe v2 v3 v1)
      MAlonzo.Code.Once.Compile.C_Error_644 v3 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct-mir
d_correct'45'mir_366 ::
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
d_correct'45'mir_366 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_correct'45'mir_366 v2 v3 v4 v5
du_correct'45'mir_366 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'mir_366 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_correct'45'cr_296
             (coe
                MAlonzo.Code.Once.Compile.d_compileFromModule_832
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Once.Compile.C_Build_634) (coe v1) (coe v0)
                (coe v2))
             erased erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct-gm
d_correct'45'gm_400 ::
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
d_correct'45'gm_400 ~v0 ~v1 v2 v3 v4 ~v5
  = du_correct'45'gm_400 v2 v3 v4
du_correct'45'gm_400 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct'45'gm_400 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             du_correct'45'mir_366 (coe v0) (coe v1) (coe v3)
             (coe
                MAlonzo.Code.Once.Adequacy.SourceTrace.d_moduleToIR_40 (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.Compile.WithCPU.correct
d_correct_426 ::
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
   MAlonzo.Code.Once.Adequacy.CPU.Interface.T_ArchSemantics_10) ->
  (MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> T_ArchCorrect_46) ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
d_correct_426 ~v0 ~v1 v2 v3 v4 = du_correct_426 v2 v3 v4
du_correct_426 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise.T_Pointwise_22
du_correct_426 v0 v1 v2
  = coe
      seq (coe v1)
      (coe
         du_correct'45'gm_400 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Grammar.ModuleConvert.d_gmoduleToModule_144
            (coe v2)))
