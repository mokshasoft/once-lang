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

-- Once.Arith.Backend.X86-64.ExecArith.InFrame
d_InFrame_10 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 -> ()
d_InFrame_10 = erased
-- Once.Arith.Backend.X86-64.ExecArith._.scratch-addr
d_scratch'45'addr_26 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
d_scratch'45'addr_26 ~v0 ~v1 v2 v3 = du_scratch'45'addr_26 v2 v3
du_scratch'45'addr_26 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  Integer
du_scratch'45'addr_26 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_220
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (coe
         mulInt (coe (8 :: Integer))
         (coe
            MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.d_slot_20 (coe v1)))
-- Once.Arith.Backend.X86-64.ExecArith._.frontier
d_frontier_32 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer
d_frontier_32 ~v0 v1 v2 = du_frontier_32 v1 v2
du_frontier_32 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer
du_frontier_32 v0 v1
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_220
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
            (coe v1))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (coe v0)
-- Once.Arith.Backend.X86-64.ExecArith._.scratch-below
d_scratch'45'below_44 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XScratch_16 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_scratch'45'below_44 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_scratch'45'below_44 v2 v8
du_scratch'45'below_44 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_scratch'45'below_44 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_220
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
            (coe v0))
         (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
      (coe v1)
-- Once.Arith.Backend.X86-64.ExecArith._.exec1
d_exec1_68 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356
d_exec1_68 v0 ~v1 v2 v3 = du_exec1_68 v0 v2 v3
du_exec1_68 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356
du_exec1_68 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_378
      (coe
         MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_step'45'of_110
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_254
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_writes_10 v1
         (coe v0 v1 v2)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
            (coe v2)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.MemEffectCore.du_mem'45'effect_60
         (coe
            (\ v3 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_370
                 (coe v3)))
         (coe
            (\ v3 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
                 (coe v3)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_220)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeMem_330)
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10)
         (coe du_scratch'45'addr_26) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_flags_372
         (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_pc_374
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_376
         (coe v2))
-- Once.Arith.Backend.X86-64.ExecArith._.Valid
d_Valid_74 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer -> ()
d_Valid_74 = erased
-- Once.Arith.Backend.X86-64.ExecArith._.exec1-preserves
d_exec1'45'preserves_84 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_exec1'45'preserves_84 v0 ~v1 v2 v3 v4 ~v5 v6 v7
  = du_exec1'45'preserves_84 v0 v2 v3 v4 v6 v7
du_exec1'45'preserves_84 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
du_exec1'45'preserves_84 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.C_mkPresState_72
      (coe
         MAlonzo.Code.Once.Arith.Backend.PreserveCore.du_step'45'of'45'preserves_122
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_254
         erased erased erased
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_writes_10
         MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Confine.d_confined_60 v1
         (coe v0 v1 v2)
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
            (coe v2)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.MemEffectCore.du_mem'45'preserves_76
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_370
                 (coe v6)))
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
                 (coe v6)))
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_220)
         erased erased
         (coe
            MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'reg_10)
         (coe du_scratch'45'addr_26)
         (\ v6 v7 v8 v9 v10 v11 v12 -> coe du_scratch'45'below_44 v6 v12)
         (coe v1) (coe v2) (coe v3) erased (coe v4) (coe v5))
-- Once.Arith.Backend.X86-64.ExecArith._.frontier-inv
d_frontier'45'inv_104 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'inv_104 = erased
-- Once.Arith.Backend.X86-64.ExecArith._.valid-inv
d_valid'45'inv_122 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_valid'45'inv_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_valid'45'inv_122 v6
du_valid'45'inv_122 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_valid'45'inv_122 v0 = coe v0
-- Once.Arith.Backend.X86-64.ExecArith._._.exec-block
d_exec'45'block_134 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356
d_exec'45'block_134 v0 ~v1 = du_exec'45'block_134 v0
du_exec'45'block_134 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356
du_exec'45'block_134 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block_60
      (coe du_exec1_68 (coe v0))
-- Once.Arith.Backend.X86-64.ExecArith._._.exec-block-preserves
d_exec'45'block'45'preserves_136 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  Integer ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_exec'45'block'45'preserves_136 v0 ~v1
  = du_exec'45'block'45'preserves_136 v0
du_exec'45'block'45'preserves_136 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
   MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_356 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
du_exec'45'block'45'preserves_136 v0
  = coe
      MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block'45'preserves_76
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'refl_78
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
                 (coe v1)))
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_370
                 (coe v1)))
         erased erased)
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'trans_92
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_368
                 (coe v1)))
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_370
                 (coe v1)))
         erased erased)
      (coe du_exec1_68 (coe v0))
      (\ v1 v2 v3 v4 v5 v6 ->
         coe du_exec1'45'preserves_84 (coe v0) v1 v2 v3 v5 v6)
      (coe (\ v1 v2 v3 v4 v5 v6 -> v5))
