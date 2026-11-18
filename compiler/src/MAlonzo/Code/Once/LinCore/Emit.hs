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

module MAlonzo.Code.Once.LinCore.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CCC.Codegen.RoomChecks
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.ExprBuild
import qualified MAlonzo.Code.Once.LinCore.ImageBlocks
import qualified MAlonzo.Code.Once.LinCore.Keys
import qualified MAlonzo.Code.Once.LinCore.Loader
import qualified MAlonzo.Code.Once.LinCore.Lower
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.Backend
import qualified MAlonzo.Code.Once.Target.Backends

-- Once.LinCore.Emit.At.imageOf
d_imageOf_80 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2322]
d_imageOf_80 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_84
      (coe
         MAlonzo.Code.Once.LinCore.Lower.d_image_2694 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1434
            (coe du_t_90 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1436
            (coe du_t_90 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1656 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1438
               (coe du_t_90 (coe v0) (coe v1)))
            (coe v2) (coe v3))
         (coe MAlonzo.Code.Once.LinCore.Loader.d_ldConst_10))
-- Once.LinCore.Emit.At._.t
d_t_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
d_t_90 v0 v1 ~v2 ~v3 = du_t_90 v0 v1
du_t_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
du_t_90 v0 v1
  = coe
      MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1612 (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.LinCore.Emit.At.blocksOf
d_blocksOf_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_blocksOf_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.ImageBlocks.du_imageBlocks_66
      (coe
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2014 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1434
            (coe du_t_104 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1436
            (coe du_t_104 (coe v0) (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1656 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1438
               (coe du_t_104 (coe v0) (coe v1)))
            (coe v2) (coe v3)))
-- Once.LinCore.Emit.At._.t
d_t_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
d_t_104 v0 v1 ~v2 ~v3 = du_t_104 v0 v1
du_t_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
du_t_104 v0 v1
  = coe
      MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1612 (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.LinCore.Emit.fileOf
d_fileOf_112 ::
  MAlonzo.Code.Once.Target.Backend.T_Backend_6 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_fileOf_112 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Target.Backend.d_file_26 v0
      (d_imageOf_80 (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Once.Target.Backend.du_file'45'table_32
         (coe MAlonzo.Code.Once.Target.Backend.d_payload_24 (coe v0))
         (coe d_blocksOf_94 (coe v1) (coe v2) (coe v3) (coe v4)))
      v5
-- Once.LinCore.Emit.emitCore
d_emitCore_126 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_652 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_emitCore_126 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Target.Backend.d_print_20
      (MAlonzo.Code.Once.Target.Backends.d_backend_6 (coe v0))
      (d_fileOf_112
         (coe MAlonzo.Code.Once.Target.Backends.d_backend_6 (coe v0))
         (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Once.Compile.d_prog'45'externs_1422 (coe v4)))
-- Once.LinCore.Emit.fileCore
d_fileCore_138 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_fileCore_138 v0 v1
  = coe
      d_after_198 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Compile.d_compileFileFromModule_1606
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v1))
-- Once.LinCore.Emit._.at
d_at_150 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_538] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_at_150 v0 ~v1 v2 v3 v4 v5 v6 = du_at_150 v0 v2 v3 v4 v5 v6
du_at_150 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_538] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_at_150 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              d_emitCore_126 (coe v0) (coe v1) (coe v7) (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Program.C_irProgram_662
                                 (coe MAlonzo.Code.Once.Compile.d_tableOf_1328 (coe v2)) (coe v9)))
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              ("internal error: the sources' main is not the program's"
                               ::
                               Data.Text.Text))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       ("internal error: the sources' main is not the program's"
                        ::
                        Data.Text.Text))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Once.Compile.d_printFile_1432 v0 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit._.core
d_core_182 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_core_182 v0 ~v1 v2 v3 v4 = du_core_182 v0 v2 v3 v4
du_core_182 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_core_182 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v2
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    du_at_150 (coe v0) (coe v4) (coe v5)
                    (coe MAlonzo.Code.Once.CompileSrc.d_mainOf_1810 (coe v4))
                    (coe MAlonzo.Code.Once.Compile.d_findMain_1294 (coe v5)) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit._.after
d_after_198 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_after_198 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             du_core_182 (coe v0)
             (coe
                MAlonzo.Code.Once.CompileSrc.d_srcModule_1760
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1))
             (coe
                MAlonzo.Code.Once.Compile.d_compileResolvedModule_1056
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.assemblyCore
d_assemblyCore_204 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_assemblyCore_204 v0 v1 = coe d_fileCore_138 (coe v0) (coe v1)
