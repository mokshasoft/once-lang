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

module MAlonzo.Code.Once.Adequacy.FileWF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.EmitFile
import qualified MAlonzo.Code.Once.Adequacy.ImageResolved
import qualified MAlonzo.Code.Once.Adequacy.ImageWF
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts
import qualified MAlonzo.Code.Once.CCC.Machine.FrameFree
import qualified MAlonzo.Code.Once.CCC.Machine.NoNested
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.FileWF._.fns-frame-free
d_fns'45'frame'45'free_8 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fns'45'frame'45'free_8
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.du_fns'45'frame'45'free_52
-- Once.Adequacy.FileWF._.image-frame-free
d_image'45'frame'45'free_10 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'frame'45'free_10
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.d_image'45'frame'45'free_76
      (coe MAlonzo.Code.Once.Compile.d_entry'45'owner_930)
-- Once.Adequacy.FileWF.map-fst
d_map'45'fst_24 ::
  () ->
  () ->
  () ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'fst_24 = erased
-- Once.Adequacy.FileWF.prog-nn
d_prog'45'nn_40 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prog'45'nn_40 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.NoNested.d_no'45'nested'45'of'45'all_22
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_42
         (coe MAlonzo.Code.Once.Compile.d_entry'45'owner_930)
         (coe
            MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
            (coe
               MAlonzo.Code.Once.Compile.d_rewrite'45'table_890
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                  (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1)))))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.d_image'45'frame'45'free_76
         (coe MAlonzo.Code.Once.Compile.d_entry'45'owner_930)
         (coe
            MAlonzo.Code.Once.Compile.d_rewrite'45'table_890
            (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
               (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v1))))
-- Once.Adequacy.FileWF.lib-nn
d_lib'45'nn_48 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> AgdaAny
d_lib'45'nn_48 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.NoNested.d_no'45'nested'45'of'45'all_22
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Compile.d_rewrite'45'table_890
            (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Machine.FrameFree.d_emittable'45'image_30
                 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
            (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Once.Compile.d_rewrite'45'table_890
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0))))
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ProgramImageFacts.du_fns'45'frame'45'free_52
            (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Once.Compile.d_rewrite'45'table_890
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)))))
-- Once.Adequacy.FileWF.resolved-at
d_resolved'45'at_66 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_resolved'45'at_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_resolved'45'at_66 v7
du_resolved'45'at_66 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_resolved'45'at_66 v0 = coe v0
-- Once.Adequacy.FileWF.X8664W.prog-wf
d_prog'45'wf_76 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
d_prog'45'wf_76 v0 v1 ~v2 = du_prog'45'wf_76 v0 v1
du_prog'45'wf_76 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
du_prog'45'wf_76 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_constructor_148
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_prog'45'unique_58 v0 v1
         erased)
      (coe
         MAlonzo.Code.Once.Adequacy.ImageResolved.du_prog'45'resolved_364
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.FileWF.X8664W._.p
d_p_88 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_88 v0 v1 ~v2 = du_p_88 v0 v1
du_p_88 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_p_88 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)) (coe v1)
-- Once.Adequacy.FileWF.X8664W._.G
d_G_90 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12
d_G_90 v0 v1 ~v2 = du_G_90 v0 v1
du_G_90 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12
du_G_90 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_emitProgram_1002
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe du_p_88 (coe v0) (coe v1))
      (MAlonzo.Code.Once.Adequacy.EmitFile.d_moduleExterns_10 (coe v0))
-- Once.Adequacy.FileWF.X8664W._.code≡
d_code'8801'_92 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'8801'_92 = erased
-- Once.Adequacy.FileWF.X8664W._.defs≡
d_defs'8801'_94 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defs'8801'_94 = erased
-- Once.Adequacy.FileWF.X8664W._.refs≡
d_refs'8801'_98 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'8801'_98 = erased
-- Once.Adequacy.FileWF.X8664W.lib-wf
d_lib'45'wf_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
d_lib'45'wf_102 v0 ~v1 = du_lib'45'wf_102 v0
du_lib'45'wf_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
du_lib'45'wf_102 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_constructor_148
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'unique_70 v0 erased)
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'resolved_74 v0 erased)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.FileWF.X8664W._.G
d_G_112 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12
d_G_112 v0 ~v1 = du_G_112 v0
du_G_112 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12
du_G_112 v0
  = coe
      MAlonzo.Code.Once.Compile.d_emitLibrary_1020
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8)
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.EmitFile.d_moduleExterns_10 (coe v0))
-- Once.Adequacy.FileWF.X8664W._.code≡
d_code'8801'_114 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'8801'_114 = erased
-- Once.Adequacy.FileWF.X8664W._.defs≡
d_defs'8801'_116 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defs'8801'_116 = erased
-- Once.Adequacy.FileWF.X8664W._.refs≡
d_refs'8801'_120 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'8801'_120 = erased
-- Once.Adequacy.FileWF.X8664W.file-wf
d_file'45'wf_126 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
d_file'45'wf_126 v0 ~v1 ~v2 = du_file'45'wf_126 v0
du_file'45'wf_126 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
du_file'45'wf_126 v0
  = coe
      du_by_140 (coe v0)
      (coe MAlonzo.Code.Once.Compile.d_moduleToIR_838 (coe v0))
-- Once.Adequacy.FileWF.X8664W._.by
d_by_140 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
d_by_140 v0 ~v1 ~v2 v3 ~v4 = du_by_140 v0 v3
du_by_140 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_AsmWF_128
du_by_140 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_prog'45'wf_76 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_lib'45'wf_102 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FileWF.X8632W.prog-wf
d_prog'45'wf_154 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
d_prog'45'wf_154 v0 v1 ~v2 = du_prog'45'wf_154 v0 v1
du_prog'45'wf_154 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
du_prog'45'wf_154 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_constructor_148
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_prog'45'unique_58 v0 v1
         erased)
      (coe
         MAlonzo.Code.Once.Adequacy.ImageResolved.du_prog'45'resolved_364
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.FileWF.X8632W._.p
d_p_166 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_166 v0 v1 ~v2 = du_p_166 v0 v1
du_p_166 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_p_166 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)) (coe v1)
-- Once.Adequacy.FileWF.X8632W._.G
d_G_168 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12
d_G_168 v0 v1 ~v2 = du_G_168 v0 v1
du_G_168 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12
du_G_168 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_emitProgram_1002
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe du_p_166 (coe v0) (coe v1))
      (MAlonzo.Code.Once.Adequacy.EmitFile.d_moduleExterns_10 (coe v0))
-- Once.Adequacy.FileWF.X8632W._.code≡
d_code'8801'_170 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'8801'_170 = erased
-- Once.Adequacy.FileWF.X8632W._.defs≡
d_defs'8801'_172 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defs'8801'_172 = erased
-- Once.Adequacy.FileWF.X8632W._.refs≡
d_refs'8801'_176 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'8801'_176 = erased
-- Once.Adequacy.FileWF.X8632W.lib-wf
d_lib'45'wf_180 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
d_lib'45'wf_180 v0 ~v1 = du_lib'45'wf_180 v0
du_lib'45'wf_180 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
du_lib'45'wf_180 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_constructor_148
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'unique_70 v0 erased)
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'resolved_74 v0 erased)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.FileWF.X8632W._.G
d_G_190 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12
d_G_190 v0 ~v1 = du_G_190 v0
du_G_190 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12
du_G_190 v0
  = coe
      MAlonzo.Code.Once.Compile.d_emitLibrary_1020
      (coe MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10)
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.EmitFile.d_moduleExterns_10 (coe v0))
-- Once.Adequacy.FileWF.X8632W._.code≡
d_code'8801'_192 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'8801'_192 = erased
-- Once.Adequacy.FileWF.X8632W._.defs≡
d_defs'8801'_194 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defs'8801'_194 = erased
-- Once.Adequacy.FileWF.X8632W._.refs≡
d_refs'8801'_198 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'8801'_198 = erased
-- Once.Adequacy.FileWF.X8632W.file-wf
d_file'45'wf_204 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
d_file'45'wf_204 v0 ~v1 ~v2 = du_file'45'wf_204 v0
du_file'45'wf_204 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
du_file'45'wf_204 v0
  = coe
      du_by_218 (coe v0)
      (coe MAlonzo.Code.Once.Compile.d_moduleToIR_838 (coe v0))
-- Once.Adequacy.FileWF.X8632W._.by
d_by_218 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
d_by_218 v0 ~v1 ~v2 v3 ~v4 = du_by_218 v0 v3
du_by_218 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_AsmWF_128
du_by_218 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_prog'45'wf_154 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_lib'45'wf_180 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FileWF.RiscV64W.prog-wf
d_prog'45'wf_232 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
d_prog'45'wf_232 v0 v1 ~v2 = du_prog'45'wf_232 v0 v1
du_prog'45'wf_232 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
du_prog'45'wf_232 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_constructor_148
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_prog'45'unique_58 v0 v1
         erased)
      (coe
         MAlonzo.Code.Once.Adequacy.ImageResolved.du_prog'45'resolved_364
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.Adequacy.FileWF.RiscV64W._.p
d_p_244 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_p_244 v0 v1 ~v2 = du_p_244 v0 v1
du_p_244 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
du_p_244 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)) (coe v1)
-- Once.Adequacy.FileWF.RiscV64W._.G
d_G_246 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12
d_G_246 v0 v1 ~v2 = du_G_246 v0 v1
du_G_246 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12
du_G_246 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_emitProgram_1002
      (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe du_p_244 (coe v0) (coe v1))
      (MAlonzo.Code.Once.Adequacy.EmitFile.d_moduleExterns_10 (coe v0))
-- Once.Adequacy.FileWF.RiscV64W._.code≡
d_code'8801'_248 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'8801'_248 = erased
-- Once.Adequacy.FileWF.RiscV64W._.defs≡
d_defs'8801'_250 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defs'8801'_250 = erased
-- Once.Adequacy.FileWF.RiscV64W._.refs≡
d_refs'8801'_254 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'8801'_254 = erased
-- Once.Adequacy.FileWF.RiscV64W.lib-wf
d_lib'45'wf_258 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
d_lib'45'wf_258 v0 ~v1 = du_lib'45'wf_258 v0
du_lib'45'wf_258 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
du_lib'45'wf_258 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_constructor_148
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'unique_70 v0 erased)
      (coe
         MAlonzo.Code.Once.Adequacy.ImageWF.d_lib'45'resolved_74 v0 erased)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.FileWF.RiscV64W._.G
d_G_268 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12
d_G_268 v0 ~v1 = du_G_268 v0
du_G_268 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12
du_G_268 v0
  = coe
      MAlonzo.Code.Once.Compile.d_emitLibrary_1020
      (coe MAlonzo.Code.Once.Target.Arch.C_riscv64_12)
      (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.EmitFile.d_moduleExterns_10 (coe v0))
-- Once.Adequacy.FileWF.RiscV64W._.code≡
d_code'8801'_270 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_code'8801'_270 = erased
-- Once.Adequacy.FileWF.RiscV64W._.defs≡
d_defs'8801'_272 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_defs'8801'_272 = erased
-- Once.Adequacy.FileWF.RiscV64W._.refs≡
d_refs'8801'_276 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refs'8801'_276 = erased
-- Once.Adequacy.FileWF.RiscV64W.file-wf
d_file'45'wf_282 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
d_file'45'wf_282 v0 ~v1 ~v2 = du_file'45'wf_282 v0
du_file'45'wf_282 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
du_file'45'wf_282 v0
  = coe
      du_by_296 (coe v0)
      (coe MAlonzo.Code.Once.Compile.d_moduleToIR_838 (coe v0))
-- Once.Adequacy.FileWF.RiscV64W._.by
d_by_296 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
d_by_296 v0 ~v1 ~v2 v3 ~v4 = du_by_296 v0 v3
du_by_296 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_AsmWF_128
du_by_296 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_prog'45'wf_232 (coe v0) (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_lib'45'wf_258 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FileWF.file-wf
d_file'45'wf_310 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_file'45'wf_310 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe (\ v1 v2 v3 -> coe du_file'45'wf_126 v1)
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe (\ v1 v2 v3 -> coe du_file'45'wf_204 v1)
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe (\ v1 v2 v3 -> coe du_file'45'wf_282 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
