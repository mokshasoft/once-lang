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

module MAlonzo.Code.Once.Arith.Backend.RiscV64.Dispatch where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Backend.ExecArithCore
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith
import qualified MAlonzo.Code.Once.Arith.Backend.StatePreserveCore
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg

-- Once.Arith.Backend.RiscV64.Dispatch._.ArithEnv
d_ArithEnv_16 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  ()
d_ArithEnv_16 = erased
-- Once.Arith.Backend.RiscV64.Dispatch._.dispatch-arith
d_dispatch'45'arith_18 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386
d_dispatch'45'arith_18 v0 v1 ~v2 v3
  = du_dispatch'45'arith_18 v0 v1 v3
du_dispatch'45'arith_18 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386
du_dispatch'45'arith_18 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.C_mkstate_404
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396
         (coe
            MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block_60
            (coe
               MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1_68
               (coe v0))
            (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
         (coe
            MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block_60
            (coe
               MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1_68
               (coe v0))
            (coe v1) (coe v2)))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_400 (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_halted_402
         (coe
            MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block_60
            (coe
               MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1_68
               (coe v0))
            (coe v1) (coe v2)))
-- Once.Arith.Backend.RiscV64.Dispatch._.step-instr
d_step'45'instr_26 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10 ->
  Maybe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386
d_step'45'instr_26 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_execInstr_522
              (coe v2) (coe v3) (coe v4) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_44 v6
           -> let v7 = coe v1 v6 in
              coe
                (case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                     -> case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe du_dispatch'45'arith_18 (coe v0) (coe v9) (coe v3))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_execInstr_522
                          (coe v2) (coe v3) (coe v4)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> coe v5)
-- Once.Arith.Backend.RiscV64.Dispatch._.step-wp
d_step'45'wp_68 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  Maybe MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386
d_step'45'wp_68 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_fetch_464
              (coe v2)
              (coe
                 MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_400
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> coe
                d_step'45'instr_26 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.C_mkstate_404
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396 (coe v3))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_pc_400 (coe v3))
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Backend.RiscV64.Dispatch._.dispatch-arith-preserves
d_dispatch'45'arith'45'preserves_100 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_dispatch'45'arith'45'preserves_100 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.C_mkPresState_72
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.d_regs'8776'_68
         (coe
            d_P_116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.d_mem'8776'_70
         (coe
            d_P_116 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)))
-- Once.Arith.Backend.RiscV64.Dispatch._._.P
d_P_116 ::
  (MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24 ->
   MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
   MAlonzo.Code.Once.Target.RiscV64.PhysReg.T_Reg_8 -> Integer) ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_386 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_P_116 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Arith.Backend.ExecArithCore.du_exec'45'block'45'preserves_76
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'refl_78
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396
                 (coe v6)))
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
                 (coe v6)))
         erased erased)
      (coe
         MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'trans_92
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396
                 (coe v6)))
         (coe
            (\ v6 ->
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_398
                 (coe v6)))
         erased erased)
      (coe
         MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1_68
         (coe v0))
      (\ v6 v7 v8 v9 v10 v11 ->
         coe
           MAlonzo.Code.Once.Arith.Backend.RiscV64.ExecArith.du_exec1'45'preserves_84
           (coe v0) v6 v7 v8 v10 v11)
      (coe (\ v6 v7 v8 v9 v10 v11 -> v10)) (coe v1)
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_readReg_236
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_396 (coe v3))
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14))
         (coe v2))
      (coe v3) erased (coe v4) (coe v5)
