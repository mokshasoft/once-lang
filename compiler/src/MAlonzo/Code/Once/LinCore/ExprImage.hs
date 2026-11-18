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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2322]
d_imageAt_10 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.Lower.d_image_2694 (coe v0)
      (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1434
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1436
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1656 (coe v0)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1438
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
               (coe v1)))
         (coe v2) (coe v3))
      (coe MAlonzo.Code.Once.LinCore.Loader.d_ldConst_10)
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
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2014 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1434
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
               (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1436
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
               (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1656 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1438
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
                  (coe v1)))
            (coe v2) (coe v3)))
-- Once.LinCore.ExprImage.fileAt
d_fileAt_28 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Target.Backend.T_Backend_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_fileAt_28 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Target.Backend.d_file_28 v1
      (MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_84
         (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Once.Target.Backend.du_file'45'table_36
         (coe MAlonzo.Code.Once.Target.Backend.d_payload_26 (coe v1))
         (coe d_blocksAt_18 (coe v0) (coe v2) (coe v3) (coe v4)))
      v5
