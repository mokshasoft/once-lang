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

module MAlonzo.Code.Once.Adequacy.ImageValid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageSymbols
import qualified MAlonzo.Code.Once.CCC.Codegen.NodesOK
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.SymbolValid
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ImageValid.ctrl-defs-asm
d_ctrl'45'defs'45'asm_8 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_FlatCtrl_2226 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ctrl'45'defs'45'asm_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v1
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (MAlonzo.Code.Once.Target.SymbolValid.d_once'45'label'45'asm_274
                (coe v1))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Once.Target.SymbolValid.d_callee'45'label'45'asm_280
                v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.instr-defs-asm
d_instr'45'defs'45'asm_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_instr'45'defs'45'asm_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2268 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2272 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2274 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2276 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2278 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2280
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2284 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2286 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2288 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2290 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 v1 v2 v3
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302 v1 v2 v3
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2310 v1 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2314 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316 v1
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v1
        -> coe d_ctrl'45'defs'45'asm_8 (coe v1)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2320 v1
        -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.adefs-asm
d_adefs'45'asm_66 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_adefs'45'asm_66 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_instr'45'defs_26
                (coe v1))
             (coe d_instr'45'defs'45'asm_16 (coe v1))
             (coe d_adefs'45'asm_66 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.dedup-step
d_dedup'45'step_90 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dedup'45'step_90 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_dedup'45'step_90 v5 v6 v7 v8
du_dedup'45'step_90 ::
  Bool ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dedup'45'step_90 v0 v1 v2 v3
  = if coe v0
      then coe v3
      else coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v1 v2
-- Once.Adequacy.ImageValid.dedup-all
d_dedup'45'all_130 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dedup'45'all_130 ~v0 v1 v2 v3 = du_dedup'45'all_130 v1 v2 v3
du_dedup'45'all_130 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dedup'45'all_130 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v9 v10
                      -> coe
                           du_dedup'45'step_90
                           (coe
                              MAlonzo.Code.Data.Bool.ListAction.du_any_14
                              (coe
                                 (\ v11 ->
                                    MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                                      (coe v11) (coe v5)))
                              (coe v0))
                           (coe v9)
                           (coe
                              du_dedup'45'all_130
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v0))
                              (coe v4) (coe v10))
                           (coe du_dedup'45'all_130 (coe v0) (coe v4) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.tag
d_tag_148 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tag_148 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Compile.d_block'45'symbol_934 (coe v0))
      (coe v0)
-- Once.Adequacy.ImageValid.tagged-asm
d_tagged'45'asm_156 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tagged'45'asm_156 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (MAlonzo.Code.Once.Target.SymbolValid.d_once'45'symbol'45'own'45'asm_240
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_366
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_174 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_178 (coe v1))))
             (d_tagged'45'asm_156 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.fst-all
d_fst'45'all_168 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fst'45'all_168 ~v0 v1 v2 = du_fst'45'all_168 v1 v2
du_fst'45'all_168 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fst'45'all_168 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6
                    (coe du_fst'45'all_168 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.block-syms-asm
d_block'45'syms'45'asm_180 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_block'45'syms'45'asm_180 v0
  = coe
      du_fst'45'all_168
      (coe
         MAlonzo.Code.Once.Compile.d_dedup'45'blocks_932
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_148) (coe v0)))
      (coe
         du_dedup'45'all_130
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_tag_148) (coe v0))
         (coe d_tagged'45'asm_156 (coe v0)))
-- Once.Adequacy.ImageValid.heap-asm
d_heap'45'asm_184 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'asm_184
  = coe
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
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))))))
-- Once.Adequacy.ImageValid.start-asm
d_start'45'asm_186 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_start'45'asm_186
  = coe
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
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
-- Once.Adequacy.ImageValid.prog-defs-valid
d_prog'45'defs'45'valid_190 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_prog'45'defs'45'valid_190 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      d_heap'45'asm_184
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         d_start'45'asm_186
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
               (coe MAlonzo.Code.Once.Compile.d_image'45'of_972 (coe v0)))
            (coe
               d_adefs'45'asm_66
               (coe MAlonzo.Code.Once.Compile.d_image'45'of_972 (coe v0)))
            (coe
               d_block'45'syms'45'asm_180
               (coe MAlonzo.Code.Once.Compile.d_program'45'blocks_904 (coe v0)))))
-- Once.Adequacy.ImageValid.lib-defs-valid
d_lib'45'defs'45'valid_196 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lib'45'defs'45'valid_196 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      d_heap'45'asm_184
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'image_1016
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0))))
         (coe
            d_adefs'45'asm_66
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'image_1016
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0))))
         (coe
            d_block'45'syms'45'asm_180
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'blocks_1024
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_874 (coe v0)))))
-- Once.Adequacy.ImageValid.sigop-syms-asm
d_sigop'45'syms'45'asm_208 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_sigop'45'syms'45'asm_208 ~v0 ~v1 v2 v3
  = du_sigop'45'syms'45'asm_208 v2 v3
du_sigop'45'syms'45'asm_208 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_sigop'45'syms'45'asm_208 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (MAlonzo.Code.Once.Target.SymbolValid.d_once'45'symbol'45'path'45'asm_234
                (coe
                   MAlonzo.Code.Once.SigOp.Info.d_name_178
                   (coe
                      MAlonzo.Code.Once.Arith.SigOp.Compare.d_cmp'45'block'45'info_24
                      (coe v2))))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (MAlonzo.Code.Once.Target.SymbolValid.d_once'45'symbol'45'path'45'asm_234
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v0)))
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.calls-asm
d_calls'45'asm_218 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_calls'45'asm_218 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_leaf'45'syms'45'all_206
         (\ v1 v2 v3 -> coe du_h_232 v3)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0)))
      (coe
         du_tbl_240
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0)))
-- Once.Adequacy.ImageValid._.h
d_h_232 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_h_232 ~v0 ~v1 ~v2 v3 = du_h_232 v3
du_h_232 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_h_232 v0
  = coe
      du_sigop'45'syms'45'asm_208 (coe v0)
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
         (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v0)))
-- Once.Adequacy.ImageValid._.tbl
d_tbl_240 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_tbl_240 ~v0 v1 = du_tbl_240 v1
du_tbl_240 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_tbl_240 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1)))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.NodesOK.du_leaf'45'syms'45'all_206
                (\ v3 v4 v5 -> coe du_h_232 v5)
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1)))
             (coe du_tbl_240 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ImageValid.externs-valid
d_externs'45'valid_248 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_externs'45'valid_248 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_filter'8314'_1242
      (coe MAlonzo.Code.Once.Compile.d_is'45'extern'63'_954 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_calls'45'of_944
         (coe MAlonzo.Code.Once.Compile.d_rewrite'45'program_900 (coe v0)))
      (coe
         d_calls'45'asm_218
         (coe MAlonzo.Code.Once.Compile.d_rewrite'45'program_900 (coe v0)))
