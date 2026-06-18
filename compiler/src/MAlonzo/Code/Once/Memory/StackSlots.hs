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

module MAlonzo.Code.Once.Memory.StackSlots where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics

-- Once.Memory.StackSlots._.InStack
d_InStack_12 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> ()
d_InStack_12 = erased
-- Once.Memory.StackSlots.StackAddr
d_StackAddr_14 a0 a1 = ()
data T_StackAddr_14
  = C_stack'45'addr_24 Integer MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Memory.StackSlots.StackAddr.addr
d_addr_20 :: T_StackAddr_14 -> Integer
d_addr_20 v0
  = case coe v0 of
      C_stack'45'addr_24 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.StackSlots.StackAddr.in-stack
d_in'45'stack_22 ::
  T_StackAddr_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'stack_22 v0
  = case coe v0 of
      C_stack'45'addr_24 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Memory.StackSlots.StackPointer
d_StackPointer_26 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  ()
d_StackPointer_26 = erased
-- Once.Memory.StackSlots._.FramePreserved
d_FramePreserved_30 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> Integer -> ()
d_FramePreserved_30 = erased
-- Once.Memory.StackSlots._.StackGrew
d_StackGrew_32 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> Integer -> ()
d_StackGrew_32 = erased
-- Once.Memory.StackSlots._.frame-preserved-under-growth
d_frame'45'preserved'45'under'45'growth_34 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_frame'45'preserved'45'under'45'growth_34 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_frame'45'preserved'45'under'45'growth_130
      (coe v0)
-- Once.Memory.StackSlots._.grow
d_grow_36 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> Integer -> Integer
d_grow_36 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_grow_98 (coe v0)
-- Once.Memory.StackSlots._.grow-addr-injective
d_grow'45'addr'45'injective_38 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'addr'45'injective_38 = erased
-- Once.Memory.StackSlots._.grow-identity
d_grow'45'identity_40 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_grow'45'identity_40 = erased
-- Once.Memory.StackSlots._.grow-injective
d_grow'45'injective_42 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'injective_42 = erased
-- Once.Memory.StackSlots._.slot-in-preserved-frame
d_slot'45'in'45'preserved'45'frame_44 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> Integer -> Integer -> AgdaAny -> AgdaAny
d_slot'45'in'45'preserved'45'frame_44 v0
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_slot'45'in'45'preserved'45'frame_138
      (coe v0)
-- Once.Memory.StackSlots.slot-addr
d_slot'45'addr_46 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 -> Integer -> Integer
d_slot'45'addr_46 ~v0 v1 v2 v3 = du_slot'45'addr_46 v1 v2 v3
du_slot'45'addr_46 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 -> Integer -> Integer
du_slot'45'addr_46 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.d_grow_98 v0
      (d_addr_20 (coe v1)) v2
-- Once.Memory.StackSlots.init-slot-at-base
d_init'45'slot'45'at'45'base_54 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45'slot'45'at'45'base_54 = erased
-- Once.Memory.StackSlots.offset-distinct
d_offset'45'distinct_64 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_offset'45'distinct_64 = erased
-- Once.Memory.StackSlots.sp-distinct
d_sp'45'distinct_80 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 ->
  T_StackAddr_14 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sp'45'distinct_80 = erased
-- Once.Memory.StackSlots.slot-in-stack-0
d_slot'45'in'45'stack'45'0_92 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_slot'45'in'45'stack'45'0_92 ~v0 ~v1 v2
  = du_slot'45'in'45'stack'45'0_92 v2
du_slot'45'in'45'stack'45'0_92 ::
  T_StackAddr_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_slot'45'in'45'stack'45'0_92 v0 = coe d_in'45'stack_22 (coe v0)
-- Once.Memory.StackSlots.slot-in-stack
d_slot'45'in'45'stack_100 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  T_StackAddr_14 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_slot'45'in'45'stack_100 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe du_slot'45'in'45'stack'45'0_92 (coe v2)
      _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
           coe (coe d_slot'45'in'45'stack'45'suc_116 v0 v1 v2 v4 v2 v4)
-- Once.Memory.StackSlots._.slot-in-stack-suc
d_slot'45'in'45'stack'45'suc_116
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Memory.StackSlots._.slot-in-stack-suc"
-- Once.Memory.StackSlots.from-raw-stack
d_from'45'raw'45'stack_120 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30 ->
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_StackAddr_14
d_from'45'raw'45'stack_120 ~v0 ~v1 v2 v3
  = du_from'45'raw'45'stack_120 v2 v3
du_from'45'raw'45'stack_120 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_StackAddr_14
du_from'45'raw'45'stack_120 v0 v1
  = coe C_stack'45'addr_24 (coe v0) (coe v1)
-- Once.Memory.StackSlots.to-raw-stack
d_to'45'raw'45'stack_126 :: T_StackAddr_14 -> Integer
d_to'45'raw'45'stack_126 v0 = coe d_addr_20 (coe v0)
