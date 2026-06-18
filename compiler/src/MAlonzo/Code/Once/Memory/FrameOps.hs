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

module MAlonzo.Code.Once.Memory.FrameOps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Memory.Memory
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics
import qualified MAlonzo.Code.Once.Memory.StackSlots

-- Once.Memory.FrameOps._.InCode
d_InCode_12 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> ()
d_InCode_12 = erased
-- Once.Memory.FrameOps._.InHeap
d_InHeap_14 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> ()
d_InHeap_14 = erased
-- Once.Memory.FrameOps._.InStack
d_InStack_16 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> ()
d_InStack_16 = erased
-- Once.Memory.FrameOps._.StackPointer
d_StackPointer_24 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  ()
d_StackPointer_24 = erased
-- Once.Memory.FrameOps._.slot-addr
d_slot'45'addr_30 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Integer
d_slot'45'addr_30 ~v0 v1 = du_slot'45'addr_30 v1
du_slot'45'addr_30 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Integer
du_slot'45'addr_30 v0
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.du_slot'45'addr_46 (coe v0)
-- Once.Memory.FrameOps.frameSlot
d_frameSlot_32 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Maybe Integer
d_frameSlot_32 ~v0 v1 v2 v3 v4 = du_frameSlot_32 v1 v2 v3 v4
du_frameSlot_32 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Maybe Integer
du_frameSlot_32 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Memory.Memory.d_readMem_88 (coe v1)
      (coe
         MAlonzo.Code.Once.Memory.StackSlots.du_slot'45'addr_46 (coe v0)
         (coe v2) (coe v3))
-- Once.Memory.FrameOps.stackAddr-write-preserves-heap
d_stackAddr'45'write'45'preserves'45'heap_48 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stackAddr'45'write'45'preserves'45'heap_48 = erased
-- Once.Memory.FrameOps.stackAddr-write-preserves-code
d_stackAddr'45'write'45'preserves'45'code_70 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stackAddr'45'write'45'preserves'45'code_70 = erased
-- Once.Memory.FrameOps.FrameSlotInternal.init-frame-slot-at-base
d_init'45'frame'45'slot'45'at'45'base_90 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45'frame'45'slot'45'at'45'base_90 = erased
-- Once.Memory.FrameOps.FrameSlotInternal.frameSlot-is-readMem
d_frameSlot'45'is'45'readMem_102 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frameSlot'45'is'45'readMem_102 = erased
