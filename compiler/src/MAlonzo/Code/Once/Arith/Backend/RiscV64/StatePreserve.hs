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

module MAlonzo.Code.Once.Arith.Backend.RiscV64.StatePreserve where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Preserve
import qualified MAlonzo.Code.Once.Arith.Backend.StatePreserveCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics

-- Once.Arith.Backend.RiscV64.StatePreserve._.PreservesCCCState
d_PreservesCCCState_12 a0 a1 a2 = ()
-- Once.Arith.Backend.RiscV64.StatePreserve._.mem≈
d_mem'8776'_16 ::
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'8776'_16 = erased
-- Once.Arith.Backend.RiscV64.StatePreserve._.preserves-state-refl
d_preserves'45'state'45'refl_20 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_preserves'45'state'45'refl_20
  = coe
      MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'refl_78
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262
              (coe v0)))
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_264
              (coe v0)))
      erased erased
-- Once.Arith.Backend.RiscV64.StatePreserve._.preserves-state-trans
d_preserves'45'state'45'trans_22 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.T_State_252 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56 ->
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56
d_preserves'45'state'45'trans_22
  = coe
      MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.du_preserves'45'state'45'trans_92
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_regs_262
              (coe v0)))
      (coe
         (\ v0 ->
            MAlonzo.Code.Once.CCC.Target.RiscV64.Semantics.d_memory_264
              (coe v0)))
      erased erased
-- Once.Arith.Backend.RiscV64.StatePreserve._.regs≈
d_regs'8776'_24 ::
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56 ->
  MAlonzo.Code.Once.Arith.Backend.RiscV64.Preserve.T_AgreeCCC_14
d_regs'8776'_24 = erased
-- Once.Arith.Backend.RiscV64.StatePreserve._.PreservesCCCState.mem≈
d_mem'8776'_28 ::
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'8776'_28 = erased
-- Once.Arith.Backend.RiscV64.StatePreserve._.PreservesCCCState.regs≈
d_regs'8776'_30 ::
  MAlonzo.Code.Once.Arith.Backend.StatePreserveCore.T_PreservesCCCState_56 ->
  MAlonzo.Code.Once.Arith.Backend.RiscV64.Preserve.T_AgreeCCC_14
d_regs'8776'_30 = erased
