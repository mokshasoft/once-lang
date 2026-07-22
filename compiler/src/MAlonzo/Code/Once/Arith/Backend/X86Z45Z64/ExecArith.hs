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

module MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.ExecArith where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Arith.Backend.ExecArithCore
import qualified MAlonzo.Code.Once.Arith.Backend.MemEffectCore
import qualified MAlonzo.Code.Once.Arith.Backend.PreserveCore
import qualified MAlonzo.Code.Once.Arith.Backend.StatePreserveCore
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg

-- Once.Arith.Backend.X86-64.ExecArith.sub-lt
d_sub'45'lt_14 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sub'45'lt_14 v0 v1 ~v2 ~v3 = du_sub'45'lt_14 v0 v1
du_sub'45'lt_14 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sub'45'lt_14 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (let v3 = subInt (coe v1) (coe (1 :: Integer)) in
       coe
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
               (coe v2) (coe v3))))
-- Once.Arith.Backend.X86-64.ExecArith.all-InFrame
d_all'45'InFrame_24 ::
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'InFrame_24 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (d_all'45'InFrame_24 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.X86-64.ExecArith._.scratch-addr
d_scratch'45'addr_34 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_34 ~v0 v1 v2 = du_scratch'45'addr_34 v1 v2
du_scratch'45'addr_34 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
du_scratch'45'addr_34 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (mulInt
         (coe (8 :: Integer))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1))))
-- Once.Arith.Backend.X86-64.ExecArith._.frontier
d_frontier_40 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
d_frontier_40 ~v0 v1 = du_frontier_40 v1
du_frontier_40 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer
du_frontier_40 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
         (coe v0))
      (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24)
-- Once.Arith.Backend.X86-64.ExecArith._.scratch-below
d_scratch'45'below_52 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'below_52 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7
  = du_scratch'45'below_52 v2 v4
du_scratch'45'below_52 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_scratch'45'below_52 v0 v1
  = coe
      du_sub'45'lt_14 (coe v1)
      (coe
         addInt
         (coe
            addInt
            (coe
               addInt
               (coe
                  addInt
                  (coe
                     addInt
                     (coe
                        addInt
                        (coe
                           addInt
                           (coe
                              addInt (coe (8 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
                  (coe
                     MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
               (coe
                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
            (coe
               MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v0)))
-- Once.Arith.Backend.X86-64.ExecArith._.exec1
d_exec1_78 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_exec1_78 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_236
      (coe
         MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_step'45'of_110
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_writes_10 v1
         (coe v0 v1 v2)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.MemEffectCore.du_mem'45'effect_60
         (coe
            (\ v3 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                 (coe v3)))
         (coe
            (\ v3 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                 (coe v3)))
         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_188)
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10)
         (coe du_scratch'45'addr_34) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_230
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_232
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_234
         (coe v2))
-- Once.Arith.Backend.X86-64.ExecArith._.Valid
d_Valid_84 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer -> ()
d_Valid_84 = erased
-- Once.Arith.Backend.X86-64.ExecArith._.exec1-preserves
d_exec1'45'preserves_94 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_exec1'45'preserves_94 v0 v1 v2 v3 ~v4 v5 v6
  = du_exec1'45'preserves_94 v0 v1 v2 v3 v5 v6
du_exec1'45'preserves_94 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
du_exec1'45'preserves_94 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.C_mkPresState_72
      (coe
         MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_step'45'of'45'preserves_122
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_114
         erased erased erased
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_writes_10
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_confined_60 v1
         (coe v0 v1 v2)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
            (coe v2)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.MemEffectCore.du_mem'45'preserves_76
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                 (coe v6)))
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                 (coe v6)))
         (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_80)
         erased erased
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10)
         (coe du_scratch'45'addr_34)
         (\ v6 v7 v8 v9 v10 v11 v12 -> coe du_scratch'45'below_52 v7 v9)
         (coe v1) (coe v2) (coe v3) erased (coe v4) (coe v5))
-- Once.Arith.Backend.X86-64.ExecArith._.frontier-inv
d_frontier'45'inv_114 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'inv_114 = erased
-- Once.Arith.Backend.X86-64.ExecArith._.valid-inv
d_valid'45'inv_130 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_valid'45'inv_130 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_valid'45'inv_130 v5
du_valid'45'inv_130 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_valid'45'inv_130 v0 = coe v0
-- Once.Arith.Backend.X86-64.ExecArith._._.exec-block
d_exec'45'block_144 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214
d_exec'45'block_144 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block_60
      (coe d_exec1_78 (coe v0))
-- Once.Arith.Backend.X86-64.ExecArith._._.exec-block-preserves
d_exec'45'block'45'preserves_146 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_214 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_exec'45'block'45'preserves_146 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block'45'preserves_76
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'refl_78
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                 (coe v1)))
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                 (coe v1)))
         erased erased)
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'trans_92
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_226
                 (coe v1)))
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_228
                 (coe v1)))
         erased erased)
      (coe d_exec1_78 (coe v0))
      (\ v1 v2 v3 v4 v5 v6 ->
         coe du_exec1'45'preserves_94 (coe v0) v1 v2 v3 v5 v6)
      (coe (\ v1 v2 v3 v4 v5 v6 -> v5))
