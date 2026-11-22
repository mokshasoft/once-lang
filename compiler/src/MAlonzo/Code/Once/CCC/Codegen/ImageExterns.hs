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

module MAlonzo.Code.Once.CCC.Codegen.ImageExterns where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageSymbols
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Compile.Emit
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Once.Target.SymbolValid

-- Once.CCC.Codegen.ImageExterns.ext-at
d_ext'45'at_12 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ext'45'at_12 ~v0 ~v1 v2 v3 = du_ext'45'at_12 v2 v3
du_ext'45'at_12 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_ext'45'at_12 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_88
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.SigOp.Info.C_callsV_90
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_92
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_94
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.SigOp.Info.C_primV_96 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageExterns.ext-sym
d_ext'45'sym_26 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ext'45'sym_26 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2450 v2 v3 v4
           -> coe
                du_ext'45'at_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v4))
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v4)))
         _ -> coe v1)
-- Once.CCC.Codegen.ImageExterns.ext-syms
d_ext'45'syms_30 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ext'45'syms_30 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_ext'45'sym_26 (coe v1)) (coe d_ext'45'syms_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageExterns.Defs
d_Defs_36 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_Defs_36 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_entry'45'symbol_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_36 (coe v0))
            (coe MAlonzo.Code.Once.Compile.Emit.d_block'45'syms_50 (coe v1))))
-- Once.CCC.Codegen.ImageExterns.ImageWF
d_ImageWF_42 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_58] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_ImageWF_42 = erased
-- Once.CCC.Codegen.ImageExterns.image-externs
d_image'45'externs_52 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_image'45'externs_52 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170)
         (coe d_ext'45'syms_30 (coe v0)))
-- Once.CCC.Codegen.ImageExterns.ext-at-in
d_ext'45'at'45'in_64 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_250 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ext'45'at'45'in_64 ~v0 ~v1 v2 ~v3 v4
  = du_ext'45'at'45'in_64 v2 v4
du_ext'45'at'45'in_64 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_250 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_ext'45'at'45'in_64 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
-- Once.CCC.Codegen.ImageExterns.ext-in
d_ext'45'in_82 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_250 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ext'45'in_82 v0 ~v1 ~v2 v3 v4 v5 = du_ext'45'in_82 v0 v3 v4 v5
du_ext'45'in_82 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_250 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_ext'45'in_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
         (coe du_go_98 (coe v1) (coe v3) (coe v0) (coe v2)))
-- Once.CCC.Codegen.ImageExterns._.go
d_go_98 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_go_98 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 = du_go_98 v3 v5 v6 v7
du_go_98 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  MAlonzo.Code.Once.SigOp.Info.T_External_250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_go_98 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
               -> coe
                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                    (coe
                       du_ext'45'at_12
                       (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v0))
                       (coe
                          MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                          (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v0))))
                    (coe
                       du_ext'45'at'45'in_64
                       (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v0)) (coe v1))
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
               -> coe
                    MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                    (d_ext'45'sym_26 (coe v4)) (d_ext'45'syms_30 (coe v5))
                    (coe du_go_98 (coe v0) (coe v1) (coe v5) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageExterns.ext-at-asm
d_ext'45'at'45'asm_118 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ext'45'at'45'asm_118 ~v0 ~v1 v2 ~v3 v4
  = du_ext'45'at'45'asm_118 v2 v4
du_ext'45'at'45'asm_118 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ext'45'at'45'asm_118 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v2 v3 v4
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_88
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.SigOp.Info.C_callsV_90
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_92
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_94
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.SigOp.Info.C_primV_96 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageExterns.ext-sym-asm
d_ext'45'sym'45'asm_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ext'45'sym'45'asm_146 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2406
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2408
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2410
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2412
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2414 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2416 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2418
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2420
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2422 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2424 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2426 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2428 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2430 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2432 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2434
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2436
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2438 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2440 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2442 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2444 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2450 v1 v2 v3
        -> coe
             du_ext'45'at'45'asm_118
             (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v3))
             (coe
                MAlonzo.Code.Once.Target.SymbolValid.d_once'45'symbol'45'path'45'asm_234
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2456 v1 v2 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2458 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2460
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2462 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2464 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2466
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2468 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v2 v3
               -> coe
                    seq (coe v2)
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v2
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
               -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2470 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2472 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2474 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2476 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2478 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2480 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2482 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageExterns.image-externs-valid
d_image'45'externs'45'valid_158 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_image'45'externs'45'valid_158 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe
                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                             (coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))))))))))))
         (coe du_go_168 (coe v0)))
-- Once.CCC.Codegen.ImageExterns._.go
d_go_168 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_go_168 ~v0 v1 = du_go_168 v1
du_go_168 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_go_168 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe d_ext'45'sym_26 (coe v1))
             (coe d_ext'45'sym'45'asm_146 (coe v1)) (coe du_go_168 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
