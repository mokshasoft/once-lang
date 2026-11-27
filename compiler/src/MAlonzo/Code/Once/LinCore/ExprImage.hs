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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
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
import qualified MAlonzo.Code.Once.LinCore.Linear
import qualified MAlonzo.Code.Once.LinCore.Loader
import qualified MAlonzo.Code.Once.LinCore.Lower
import qualified MAlonzo.Code.Once.Spec.Name
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
      MAlonzo.Code.Once.LinCore.Lower.du_image_3096 (coe v0)
      (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1418
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1420
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1640 (coe v0)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1422
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe v2) (coe v3))
      (coe MAlonzo.Code.Once.LinCore.Loader.d_ldConst_10)
      (coe
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2802 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1418
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1420
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1640 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1422
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
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
      MAlonzo.Code.Once.LinCore.ImageBlocks.du_imageBlocks_70
      (coe
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2802 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1418
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1420
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1640 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1422
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
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
      MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_expand_128
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
      MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_expand_128
      (MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.d_classes_384
         (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_outline_162
            (coe
               MAlonzo.Code.Once.CCC.Codegen.AllocExpandClasses.d_dsizes_268
               (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4)))
            (coe d_imageAt_10 (coe v0) (coe v2) (coe v3) (coe v4))))
      (MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_outline_162
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
      (MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_166
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
-- Once.LinCore.ExprImage.linearSites
d_linearSites_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_linearSites_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246
      (coe d_perDef_110 (coe v0) (coe v1) (coe v2) (coe v3)) (coe v1)
-- Once.LinCore.ExprImage._.lc
d_lc_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
d_lc_98 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.Keys.d_lct_2512
      (coe
         MAlonzo.Code.Once.LinCore.Keys.d_univ_2802 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Loader.d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1418
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1420
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
               (coe v1)))
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1640 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1422
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1426 (coe v0)
                  (coe v1)))
            (coe v2) (coe v3)))
-- Once.LinCore.ExprImage._.nameOf
d_nameOf_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_nameOf_100 ~v0 ~v1 ~v2 ~v3 v4 = du_nameOf_100 v4
du_nameOf_100 ::
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_nameOf_100 v0
  = coe
      MAlonzo.Code.Data.String.Base.d_intersperse_30
      ("." :: Data.Text.Text)
      (MAlonzo.Code.Once.Spec.Name.d_parts_10
         (coe MAlonzo.Code.Once.CompileSrc.d_csName_1020 (coe v0)))
-- Once.LinCore.ExprImage._.vars
d_vars_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_vars_104 ~v0 ~v1 ~v2 ~v3 v4 = du_vars_104 v4
du_vars_104 ::
  [Integer] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_vars_104 v0
  = coe
      MAlonzo.Code.Data.String.Base.d_intersperse_30
      (", " :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                 ("#" :: Data.Text.Text)
                 (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)))
         (coe v0))
-- Once.LinCore.ExprImage._.perDef
d_perDef_110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_perDef_110 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v5 ->
            case coe v5 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                -> coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (coe du_nameOf_100 (coe v4))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (": " :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20 v6
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe MAlonzo.Code.Data.List.Base.du_null_262 (coe v7))
                              (coe ("" :: Data.Text.Text))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" (variables " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (coe du_vars_104 (coe v7)) (")" :: Data.Text.Text))))))
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         MAlonzo.Code.Once.LinCore.Linear.d_sites_272 (coe v0)
         (coe d_lc_98 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.CompileSrc.d_n_24
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v4)))
         (coe
            MAlonzo.Code.Once.CompileSrc.d_Γ_26
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v4)))
         (coe
            MAlonzo.Code.Once.CompileSrc.d_Ψ_28
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v4)))
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v4))
         (coe
            MAlonzo.Code.Once.CompileSrc.d_expr_36
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v4))))
