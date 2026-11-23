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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageExterns
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.LinCore.ExprBuild
import qualified MAlonzo.Code.Once.LinCore.ExprImage
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.Backend
import qualified MAlonzo.Code.Once.Target.Backends

-- Once.LinCore.Emit.fileOf
d_fileOf_16 ::
  MAlonzo.Code.Once.Target.Backend.T_Backend_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> AgdaAny
d_fileOf_16 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.LinCore.ExprImage.d_fileAt_54 (coe v3) (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1508 (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ImageExterns.d_image'45'externs_52
         (coe
            MAlonzo.Code.Once.LinCore.ExprImage.d_imageAt_10 (coe v3)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1508 (coe v4)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
            (coe v5) (coe v6)))
-- Once.LinCore.Emit.toFileOf
d_toFileOf_32 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> AgdaAny -> AgdaAny
d_toFileOf_32 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.LinCore.Emit.mainAt
d_mainAt_44 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_mainAt_44 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       d_toFileOf_32 (coe v0)
                       (coe
                          d_fileOf_16
                          (coe MAlonzo.Code.Once.Target.Backends.d_backend_6 (coe v0))
                          (coe v1) (coe v2)
                          (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                          (coe v3) (coe v6) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                ("internal error: the sources have no main the program has"
                 ::
                 Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.srcsAt
d_srcsAt_68 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcsAt_68 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             d_mainAt_44 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe MAlonzo.Code.Once.CompileSrc.d_mainOf_1810 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.coreAt
d_coreAt_88 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_coreAt_88 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_srcsAt_68 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.CompileSrc.d_srcModule_1760
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                d_toFileOf_32 (coe v0)
                (coe
                   MAlonzo.Code.Once.Target.Backend.d_empty_32
                   (coe MAlonzo.Code.Once.Target.Backends.d_backend_6 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.coreAfter
d_coreAfter_108 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_coreAfter_108 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             d_coreAt_88 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Compile.d_moduleToIR_1298 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.coreFileOf
d_coreFileOf_130 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_coreFileOf_130 v0 v1 v2 v3 v4
  = coe
      d_coreAfter_108 (coe v0) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Compile.d_checkModule_1414
         (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v1) (coe v0) (coe v4))
-- Once.LinCore.Emit.assemblyCore
d_assemblyCore_142 ::
  Bool ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_assemblyCore_142 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Compile.d_printResult_1426 (coe v3)
      (coe d_coreFileOf_130 (coe v3) (coe v0) (coe v1) (coe v2) (coe v4))
