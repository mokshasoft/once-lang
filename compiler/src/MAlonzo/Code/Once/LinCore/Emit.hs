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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Codegen.RoomChecks
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.ExprBuild
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.Keys
import qualified MAlonzo.Code.Once.LinCore.Lower
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.SubDecide
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.LinCore.Emit.bw
d_bw_6 :: MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer
d_bw_6 v0 = coe seq (coe v0) (coe (1 :: Integer))
-- Once.LinCore.Emit.ldConst
d_ldConst_10 ::
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2322
d_ldConst_10 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_int_48
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2374
             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v1)
      MAlonzo.Code.Once.LinCore.Flat.C_float_50
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2374
             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.mainOf
d_mainOf_18 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainOf_18 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_at_30 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
                (coe MAlonzo.Code.Once.CompileSrc.d_csName_1020 (coe v1))
                (coe
                   MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe ("main" :: Data.Text.Text))))
             (coe
                MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1))
                (coe MAlonzo.Code.Once.Compile.du_EffUU_1262))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit._.at
d_at_30 ::
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_30 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.CompileSrc.d_csType_1022
                                                  (coe v0))
                                               (coe v8))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe seq (coe v7) (coe d_mainOf_18 (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe d_mainOf_18 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.At._.Sig
d_Sig_100 a0 = ()
-- Once.LinCore.Emit.At._.Sig.info
d_info_108 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_108 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0)
-- Once.LinCore.Emit.At._.Sig.sA
d_sA_110 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_110 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0)
-- Once.LinCore.Emit.At._.Sig.sB
d_sB_112 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_112 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0)
-- Once.LinCore.Emit.At.imageOf
d_imageOf_122 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2322]
d_imageOf_122 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Codegen.RoomChecks.d_room'45'checks_84
      (coe
         MAlonzo.Code.Once.LinCore.Lower.d_image_2694 (coe v0) (coe d_bw_6)
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1434
            (coe du_t_132 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1436
            (coe du_t_132 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1656 (coe v0)
            (coe
               MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1438
               (coe du_t_132 (coe v0) (coe v1)))
            (coe v2) (coe v3))
         (coe d_ldConst_10))
-- Once.LinCore.Emit.At._.t
d_t_132 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
d_t_132 v0 v1 ~v2 ~v3 = du_t_132 v0 v1
du_t_132 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
du_t_132 v0 v1
  = coe
      MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1612 (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.LinCore.Emit.At.opBlocks
d_opBlocks_134 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_opBlocks_134 ~v0 v1 = du_opBlocks_134 v1
du_opBlocks_134 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_opBlocks_134 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         du_alias_142 (coe v0)
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_try'45'lift_64
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0)))
            (coe
               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0)))
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0)))
               (coe
                  MAlonzo.Code.Once.IR.C_SigOp_144
                  (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0))
                  (coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0))
                  (coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0)))
               (coe MAlonzo.Code.Once.IR.C_id_20))))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe MAlonzo.Code.Once.Compile.d_block'45'symbol_1392 (coe v1))
                 (coe v1)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Once.Arith.Machine.Rewrite.d_bare'45'at_270
                  (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0))
                  (coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0))
                  (coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Arith.Machine.Rewrite.d_try'45'lift_64
                     (coe
                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                        (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                        (coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.IR.C__'8728'__28
                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                           (coe (0 :: Integer))
                           (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0)))
                        (coe
                           MAlonzo.Code.Once.IR.C_SigOp_144
                           (coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0))
                           (coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0))
                           (coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0)))
                        (coe MAlonzo.Code.Once.IR.C_id_20)))))
            (coe
               MAlonzo.Code.Once.Arith.Machine.Rewrite.du_sigop'45'blocks_200
               (coe
                  MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_18
                  (coe
                     MAlonzo.Code.Once.SigOp.Info.d_sem_118
                     (coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0)))))))
-- Once.LinCore.Emit.At._.alias
d_alias_142 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_alias_142 ~v0 v1 v2 = du_alias_142 v1 v2
du_alias_142 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_alias_142 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                          (coe
                             MAlonzo.Code.Once.SigOp.Info.d_name_116
                             (coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0))))
                       (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.At.blocksOf
d_blocksOf_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocksOf_150 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Compile.d_dedup'45'blocks_1390
      (coe
         MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe du_opBlocks_134)
         (coe
            MAlonzo.Code.Once.LinCore.Keys.d_ops_1992
            (coe
               MAlonzo.Code.Once.LinCore.Keys.d_univ_2014 (coe v0) (coe d_bw_6)
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_L_1434
                  (coe du_t_160 (coe v0) (coe v1)))
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.d_defs_1436
                  (coe du_t_160 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
               (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
               (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
               (coe
                  MAlonzo.Code.Once.LinCore.ExprBuild.du_mainCore_1656 (coe v0)
                  (coe
                     MAlonzo.Code.Once.LinCore.ExprBuild.d_rs_1438
                     (coe du_t_160 (coe v0) (coe v1)))
                  (coe v2) (coe v3)))))
-- Once.LinCore.Emit.At._.t
d_t_160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
d_t_160 v0 v1 ~v2 ~v3 = du_t_160 v0 v1
du_t_160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.LinCore.ExprBuild.T_ETProg_1426
du_t_160 v0 v1
  = coe
      MAlonzo.Code.Once.LinCore.ExprBuild.d_exprTable_1442 (coe v0)
      (coe
         MAlonzo.Code.Once.LinCore.ExprBuild.du_srcOrder_1612 (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.LinCore.Emit.emitCore
d_emitCore_166 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_652 -> AgdaAny
d_emitCore_166 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.du_compile'45'trace'45'cnt_78
                   (coe (0 :: Integer))
                   (coe
                      d_imageOf_122
                      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                      (coe v1) (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v5 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_block'45'payload_300
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
                (coe
                   d_blocksOf_150
                   (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                   (coe v1) (coe v2) (coe v3)))
             (coe MAlonzo.Code.Once.Compile.d_prog'45'externs_1422 (coe v4))
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.du_compile'45'trace'45'cnt_128
                   (coe (0 :: Integer))
                   (coe
                      d_imageOf_122
                      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                      (coe v1) (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v5 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_block'45'payload_302
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
                (coe
                   d_blocksOf_150
                   (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                   (coe v1) (coe v2) (coe v3)))
             (coe MAlonzo.Code.Once.Compile.d_prog'45'externs_1422 (coe v4))
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe
             MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.du_compile'45'trace'45'cnt_154
                   (coe (0 :: Integer))
                   (coe
                      d_imageOf_122
                      (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                      (coe v1) (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v5 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_block'45'payload_324
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))))
                (coe
                   d_blocksOf_150
                   (coe MAlonzo.Code.Once.Target.Arch.d_arch'45'numerics_62 (coe v0))
                   (coe v1) (coe v2) (coe v3)))
             (coe MAlonzo.Code.Once.Compile.d_prog'45'externs_1422 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit.fileCore
d_fileCore_194 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_fileCore_194 v0 v1
  = coe
      d_after_254 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Compile.d_compileFileFromModule_1606
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v1))
-- Once.LinCore.Emit._.at
d_at_206 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_538] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_at_206 v0 ~v1 v2 v3 v4 v5 v6 = du_at_206 v0 v2 v3 v4 v5 v6
du_at_206 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_538] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_at_206 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              d_emitCore_166 (coe v0) (coe v1) (coe v7) (coe v8)
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
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit._.core
d_core_238 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_core_238 v0 ~v1 v2 v3 v4 = du_core_238 v0 v2 v3 v4
du_core_238 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_core_238 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v2
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    du_at_206 (coe v0) (coe v4) (coe v5) (coe d_mainOf_18 (coe v4))
                    (coe MAlonzo.Code.Once.Compile.d_findMain_1294 (coe v5)) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Emit._.after
d_after_254 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_after_254 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             du_core_238 (coe v0)
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
d_assemblyCore_260 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_assemblyCore_260 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_printResult_1618 (coe v0)
      (coe d_fileCore_194 (coe v0) (coe v1))
