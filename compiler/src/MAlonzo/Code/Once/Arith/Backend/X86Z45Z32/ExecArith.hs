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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.ExecArith where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics
import qualified MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg

-- Once.Arith.Backend.X86-32.ExecArith.writes
d_writes_10 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  [MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8]
d_writes_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_56 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_eax_10)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.ExecArith._.scratch-addr
d_scratch'45'addr_46 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_46 ~v0 v1 v2 = du_scratch'45'addr_46 v1 v2
du_scratch'45'addr_46 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
du_scratch'45'addr_46 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_202
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_302
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.C_esp_24))
      (coe
         mulInt (coe (4 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Arith.Backend.X86-32.ExecArith._.write-regs
d_write'45'regs_52 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_166 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_166
d_write'45'regs_52 ~v0 v1 v2 = du_write'45'regs_52 v1 v2
du_write'45'regs_52 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_166 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_166
du_write'45'regs_52 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_write'45'regs_52 (coe v3)
                    (coe
                       MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_writeReg_220 v1
                       v4 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-32.ExecArith._.step-of
d_step'45'of_64 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_RegFile_166
d_step'45'of_64 v0 v1 v2
  = coe
      du_write'45'regs_52
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                 (coe v0 v1 v2 v3)))
         (coe d_writes_10 (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_302
         (coe v2))
-- Once.Arith.Backend.X86-32.ExecArith._.mem-effect
d_mem'45'effect_72 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  Integer -> Maybe Integer
d_mem'45'effect_72 ~v0 v1 v2 = du_mem'45'effect_72 v1 v2
du_mem'45'effect_72 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  Integer -> Maybe Integer
du_mem'45'effect_72 v0 v1
  = let v2
          = MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_304
              (coe v1) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30 v3 v4
           -> coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_writeMem_264
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_memory_304
                   (coe v1))
                (coe du_scratch'45'addr_46 (coe v1) (coe v3))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_readReg_202
                   (coe
                      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_regs_302
                      (coe v1))
                   (coe
                      MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'reg_10
                      (coe v4)))
         _ -> coe v2)
-- Once.Arith.Backend.X86-32.ExecArith._.exec1
d_exec1_82 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290
d_exec1_82 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.C_mkstate_312
      (coe d_step'45'of_64 (coe v0) (coe v1) (coe v2))
      (coe du_mem'45'effect_72 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_flags_306
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_pc_308
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.d_halted_310
         (coe v2))
-- Once.Arith.Backend.X86-32.ExecArith._.exec-arith-block
d_exec'45'arith'45'block_88 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
   MAlonzo.Code.Once.Target.X86Z45Z32.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Semantics.T_State_290
d_exec'45'arith'45'block_88 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             d_exec'45'arith'45'block_88 (coe v0) (coe v4)
             (coe d_exec1_82 (coe v0) (coe v3) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
