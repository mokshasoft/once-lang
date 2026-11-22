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

module MAlonzo.Code.Once.Compile.Emit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.Symbol

-- Once.Compile.Emit.rewrite-fun
d_rewrite'45'fun_6 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_rewrite'45'fun_6 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_284
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
            (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v0))))
-- Once.Compile.Emit.rewrite-table
d_rewrite'45'table_10 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_rewrite'45'table_10 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_rewrite'45'fun_6 (coe v1))
             (coe d_rewrite'45'table_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.Emit.rewrite-program
d_rewrite'45'program_16 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_652 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_652
d_rewrite'45'program_16 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_662
      (coe
         d_rewrite'45'table_10
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_658 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_284
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_660 (coe v0))))
-- Once.Compile.Emit.table-blocks
d_table'45'blocks_20 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_table'45'blocks_20 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_284
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))))
             (coe d_table'45'blocks_20 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.Emit.program-blocks
d_program'45'blocks_26 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_652 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58]
d_program'45'blocks_26 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_284
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_660 (coe v0))))
      (coe
         d_table'45'blocks_20
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_658 (coe v0)))
-- Once.Compile.Emit.dedup-go
d_dedup'45'go_30 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_dedup'45'go_30 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Data.Bool.ListAction.du_any_14
                       (coe
                          (\ v6 ->
                             MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                               (coe v6) (coe v4)))
                       (coe v0))
                    (coe d_dedup'45'go_30 (coe v0) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe
                          d_dedup'45'go_30
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                          (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.Emit.dedup-blocks
d_dedup'45'blocks_44 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_dedup'45'blocks_44
  = coe
      d_dedup'45'go_30 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.Emit.block-symbol
d_block'45'symbol_46 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'symbol_46 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.d_block'45'name_114
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_66 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'kind_68 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_70 (coe v0)))
-- Once.Compile.Emit.block-syms
d_block'45'syms_50 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_block'45'syms_50 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe
         d_dedup'45'blocks_44
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_block'45'symbol_46 (coe v1)) (coe v1)))
            (coe v0)))
-- Once.Compile.Emit.entry-owner
d_entry'45'owner_56 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_entry'45'owner_56
  = coe
      MAlonzo.Code.Once.Spec.Name.d_bare_14
      (coe ("0entry" :: Data.Text.Text))
-- Once.Compile.Emit.FileOf
d_FileOf_58 :: MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> ()
d_FileOf_58 = erased
-- Once.Compile.Emit.printFile
d_printFile_62 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printFile_62 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_print_84
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_print_84
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_print_84
      _ -> MAlonzo.RTE.mazUnreachableError
