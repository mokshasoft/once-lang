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

module MAlonzo.Code.Once.LinCore.ExprImage where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocExpand
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses
import qualified MAlonzo.Code.Once.CCC.Codegen.RoomChecks
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.ExprBuild
import qualified MAlonzo.Code.Once.LinCore.ImageBlocks
import qualified MAlonzo.Code.Once.LinCore.Keys
import qualified MAlonzo.Code.Once.LinCore.Loader
import qualified MAlonzo.Code.Once.LinCore.Lower
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Target.Backend

-- Once.LinCore.ExprImage.imageAt
d_imageAt_10 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_imageAt_10 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.Lower.du_image_2812 (coe v0)
      (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1330
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1332
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1552 (coe v0)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1334
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
               (coe v1)))
         (coe v2) (coe v3))
      (coe MAlonzo.Code.Once.LinCore.Loader.d_ldConst_10)
      (coe
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2026 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1330
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
               (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1332
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
               (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1552 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1334
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
                  (coe v1)))
            (coe v2) (coe v3)))
-- Once.LinCore.ExprImage.blocksAt
d_blocksAt_18 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_blocksAt_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.ImageBlocks.du_imageBlocks_66
      (coe
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2026 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1330
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
               (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1332
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
               (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1552 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1334
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1338 (coe v0)
                  (coe v1)))
            (coe v2) (coe v3)))
-- Once.LinCore.ExprImage.imageAtˣ
d_imageAt'739'_26 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_imageAt'739'_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_expand_126
      (MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.d_classes_384
         (coe v1) (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4)))
      (d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4))
-- Once.LinCore.ExprImage.imageAtᶜ
d_imageAt'7580'_36 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_imageAt'7580'_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_expand_126
      (MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.d_classes_384
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_outline_160
            (coe
               MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.d_dsizes_268
               (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4)))
            (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4))))
      (MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_outline_160
         (coe
            MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.d_dsizes_268
            (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4)))
         (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4)))
-- Once.LinCore.ExprImage.imageAtₘ
d_imageAt'8344'_48 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430]
d_imageAt'8344'_48 v0 v1
  = if coe v1
      then coe d_imageAt'739'_26 (coe v0)
      else coe d_imageAt'7580'_36 (coe v0)
-- Once.LinCore.ExprImage.fileAt
d_fileAt_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Target.Backend.T_Backend_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_fileAt_54 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Target.Backend.d_file_30 v1
      (MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_92
         (coe d_imageAt'8344'_48 v0 v3 v2 v4 v5 v6))
      (coe
         MAlonzo.Code.Once.Target.Backend.du_file'45'table_40
         (coe MAlonzo.Code.Once.Target.Backend.d_payload_28 (coe v1))
         (coe d_blocksAt_18 (coe v0) (coe v4) (coe v5) (coe v6)))
      v7
-- Once.LinCore.ExprImage.fileAtᵘ
d_fileAt'7512'_72 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Target.Backend.T_Backend_6 ->
  MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.T_Alloc_378 ->
  Bool ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_fileAt'7512'_72 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Target.Backend.d_file_30 v1
      (coe d_imageAt'8344'_48 v0 v3 v2 v4 v5 v6)
      (coe
         MAlonzo.Code.Once.Target.Backend.du_file'45'table_40
         (coe MAlonzo.Code.Once.Target.Backend.d_payload_28 (coe v1))
         (coe d_blocksAt_18 (coe v0) (coe v4) (coe v5) (coe v6)))
      v7
