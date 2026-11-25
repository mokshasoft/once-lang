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

module MAlonzo.Code.Once.CCC.Codegen.ImageSymbols where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolFresh

-- Once.CCC.Codegen.ImageSymbols.entry-symbol
d_entry'45'symbol_8 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_entry'45'symbol_8 = coe ("once_main" :: Data.Text.Text)
-- Once.CCC.Codegen.ImageSymbols.ctrl-defs
d_ctrl'45'defs_10 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_FlatCtrl_2378 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ctrl'45'defs_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Label.d_labelSym_198
                (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Label.d_labelSym_198
                (coe MAlonzo.Code.Once.CCC.Label.C_callee_34 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageSymbols.ctrl-refs
d_ctrl'45'refs_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_FlatCtrl_2378 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ctrl'45'refs_16 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Label.d_labelSym_198
                (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Label.d_labelSym_198
                (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Label.d_labelSym_198
                (coe
                   MAlonzo.Code.Once.CCC.Label.C_callee_34
                   (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageSymbols.instr-defs
d_instr'45'defs_24 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_instr'45'defs_24 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v2
           -> coe d_ctrl'45'defs_10 (coe v2)
         _ -> coe v1)
-- Once.CCC.Codegen.ImageSymbols.part-refs
d_part'45'refs_28 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_part'45'refs_28 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Codegen.ImageSymbols.stack-refs
d_stack'45'refs_30 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_stack'45'refs_30 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.ImageSymbols.instr-refs
d_instr'45'refs_32 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_instr'45'refs_32 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2476 v2 v3 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v4)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2484 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.CCC.Label.d_thunkSym_188 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v2
           -> coe d_ctrl'45'refs_16 (coe v2)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2498 v2
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_stack'45'refs_30
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45's_2426 (coe v2)))
                (coe
                   d_part'45'refs_28
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45'h_2424 (coe v2)))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2506 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2508 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> coe v1)
-- Once.CCC.Codegen.ImageSymbols.adefs
d_adefs_42 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_adefs_42 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_instr'45'defs_24 (coe v1)) (coe d_adefs_42 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.ImageSymbols.arefs
d_arefs_48 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_arefs_48 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_instr'45'refs_32 (coe v1)) (coe d_arefs_48 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
