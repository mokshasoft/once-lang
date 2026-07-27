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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Layout where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth
import qualified MAlonzo.Code.Once.Memory.FrameOps
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics
import qualified MAlonzo.Code.Once.Memory.Regions
import qualified MAlonzo.Code.Once.Memory.RuntimeContract
import qualified MAlonzo.Code.Once.Memory.StackSlots

-- Once.CCC.Target.X86-64.Layout.x86-stack-bounds
d_x86'45'stack'45'bounds_10 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_x86'45'stack'45'bounds_10
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_stack'45'bounds_42
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams.d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.Layout.x86-heap-bounds
d_x86'45'heap'45'bounds_12 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_x86'45'heap'45'bounds_12
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_heap'45'bounds_44
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams.d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.Layout.x86-code-bounds
d_x86'45'code'45'bounds_14 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_x86'45'code'45'bounds_14
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_code'45'bounds_46
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams.d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.Layout.x86-layout
d_x86'45'layout_16 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_MemoryLayout_30
d_x86'45'layout_16
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_52
      (coe d_x86'45'stack'45'bounds_10) (coe d_x86'45'heap'45'bounds_12)
      (coe d_x86'45'code'45'bounds_14)
      (coe
         MAlonzo.Code.Once.Memory.RuntimeContract.d_intervals'45'disjoint_50
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams.d_x86'45'64'45'runtime_10))
-- Once.CCC.Target.X86-64.Layout._.HeapAddr
d_HeapAddr_20 = ()
-- Once.CCC.Target.X86-64.Layout._.HeapPointer
d_HeapPointer_24 :: ()
d_HeapPointer_24 = erased
-- Once.CCC.Target.X86-64.Layout._.InCode
d_InCode_26 :: Integer -> ()
d_InCode_26 = erased
-- Once.CCC.Target.X86-64.Layout._.InHeap
d_InHeap_28 :: Integer -> ()
d_InHeap_28 = erased
-- Once.CCC.Target.X86-64.Layout._.InStack
d_InStack_30 :: Integer -> ()
d_InStack_30 = erased
-- Once.CCC.Target.X86-64.Layout._.code-bounds
d_code'45'bounds_32 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_code'45'bounds_32
  = coe
      MAlonzo.Code.Once.Memory.Regions.d_code'45'bounds_12
      (coe d_x86'45'layout_16)
-- Once.CCC.Target.X86-64.Layout._.haddr
d_haddr_34 ::
  MAlonzo.Code.Once.Memory.Regions.T_HeapAddr_108 -> Integer
d_haddr_34 v0
  = coe MAlonzo.Code.Once.Memory.Regions.d_haddr_114 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.heap-bounds
d_heap'45'bounds_38 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_heap'45'bounds_38
  = coe
      MAlonzo.Code.Once.Memory.Regions.d_heap'45'bounds_10
      (coe d_x86'45'layout_16)
-- Once.CCC.Target.X86-64.Layout._.heap-code-addr-disjoint
d_heap'45'code'45'addr'45'disjoint_40 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'45'code'45'addr'45'disjoint_40 = erased
-- Once.CCC.Target.X86-64.Layout._.heap-code-disjoint
d_heap'45'code'45'disjoint_42 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_heap'45'code'45'disjoint_42 = erased
-- Once.CCC.Target.X86-64.Layout._.in-heap
d_in'45'heap_44 ::
  MAlonzo.Code.Once.Memory.Regions.T_HeapAddr_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'heap_44 v0
  = coe MAlonzo.Code.Once.Memory.Regions.d_in'45'heap_116 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.intervals-disjoint
d_intervals'45'disjoint_46 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_intervals'45'disjoint_46
  = coe
      MAlonzo.Code.Once.Memory.Regions.d_intervals'45'disjoint_28
      (coe d_x86'45'layout_16)
-- Once.CCC.Target.X86-64.Layout._.stack-bounds
d_stack'45'bounds_48 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_RegionBounds_8
d_stack'45'bounds_48
  = coe
      MAlonzo.Code.Once.Memory.Regions.d_stack'45'bounds_8
      (coe d_x86'45'layout_16)
-- Once.CCC.Target.X86-64.Layout._.stack-code-addr-disjoint
d_stack'45'code'45'addr'45'disjoint_50 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'code'45'addr'45'disjoint_50 = erased
-- Once.CCC.Target.X86-64.Layout._.stack-code-disjoint
d_stack'45'code'45'disjoint_52 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'code'45'disjoint_52 = erased
-- Once.CCC.Target.X86-64.Layout._.stack-heap-addr-disjoint
d_stack'45'heap'45'addr'45'disjoint_54 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'heap'45'addr'45'disjoint_54 = erased
-- Once.CCC.Target.X86-64.Layout._.stack-heap-disjoint
d_stack'45'heap'45'disjoint_56 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stack'45'heap'45'disjoint_56 = erased
-- Once.CCC.Target.X86-64.Layout._.HeapAddr.haddr
d_haddr_60 ::
  MAlonzo.Code.Once.Memory.Regions.T_HeapAddr_108 -> Integer
d_haddr_60 v0
  = coe MAlonzo.Code.Once.Memory.Regions.d_haddr_114 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.HeapAddr.in-heap
d_in'45'heap_62 ::
  MAlonzo.Code.Once.Memory.Regions.T_HeapAddr_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'heap_62 v0
  = coe MAlonzo.Code.Once.Memory.Regions.d_in'45'heap_116 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.FramePreserved
d_FramePreserved_66 :: Integer -> Integer -> ()
d_FramePreserved_66 = erased
-- Once.CCC.Target.X86-64.Layout._.StackAddr
d_StackAddr_68 = ()
-- Once.CCC.Target.X86-64.Layout._.StackGrew
d_StackGrew_72 :: Integer -> Integer -> ()
d_StackGrew_72 = erased
-- Once.CCC.Target.X86-64.Layout._.StackPointer
d_StackPointer_74 :: ()
d_StackPointer_74 = erased
-- Once.CCC.Target.X86-64.Layout._.addr
d_addr_76 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> Integer
d_addr_76 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.frame-preserved-under-growth
d_frame'45'preserved'45'under'45'growth_78 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame'45'preserved'45'under'45'growth_78 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth.du_x86'45'frame'45'preserved'45'under'45'growth_90
      v3 v4
-- Once.CCC.Target.X86-64.Layout._.from-raw-stack
d_from'45'raw'45'stack_80 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_from'45'raw'45'stack_80
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.du_from'45'raw'45'stack_120
-- Once.CCC.Target.X86-64.Layout._.grow
d_grow_82 :: Integer -> Integer -> Integer
d_grow_82
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth.d_x86'45'grow_12
-- Once.CCC.Target.X86-64.Layout._.grow-addr-injective
d_grow'45'addr'45'injective_84 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'addr'45'injective_84 = erased
-- Once.CCC.Target.X86-64.Layout._.grow-identity
d_grow'45'identity_86 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_grow'45'identity_86 = erased
-- Once.CCC.Target.X86-64.Layout._.grow-injective
d_grow'45'injective_88 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_grow'45'injective_88 = erased
-- Once.CCC.Target.X86-64.Layout._.in-stack
d_in'45'stack_90 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'stack_90 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_in'45'stack_22 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.init-slot-at-base
d_init'45'slot'45'at'45'base_92 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45'slot'45'at'45'base_92 = erased
-- Once.CCC.Target.X86-64.Layout._.offset-distinct
d_offset'45'distinct_94 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_offset'45'distinct_94 = erased
-- Once.CCC.Target.X86-64.Layout._.slot-addr
d_slot'45'addr_96 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Integer
d_slot'45'addr_96
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.du_slot'45'addr_46
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth.d_x86'45'stack'45'growth_118)
-- Once.CCC.Target.X86-64.Layout._.slot-in-preserved-frame
d_slot'45'in'45'preserved'45'frame_98 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'in'45'preserved'45'frame_98 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth.du_x86'45'slot'45'in'45'preserved'45'frame_108
      v0 v3
-- Once.CCC.Target.X86-64.Layout._.slot-in-stack
d_slot'45'in'45'stack_100 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_slot'45'in'45'stack_100
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.d_slot'45'in'45'stack_100
      (coe d_x86'45'layout_16)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth.d_x86'45'stack'45'growth_118)
-- Once.CCC.Target.X86-64.Layout._.slot-in-stack-0
d_slot'45'in'45'stack'45'0_102 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_slot'45'in'45'stack'45'0_102
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.du_slot'45'in'45'stack'45'0_92
-- Once.CCC.Target.X86-64.Layout._.sp-distinct
d_sp'45'distinct_104 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sp'45'distinct_104 = erased
-- Once.CCC.Target.X86-64.Layout._.to-raw-stack
d_to'45'raw'45'stack_108 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> Integer
d_to'45'raw'45'stack_108 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.StackAddr.addr
d_addr_112 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> Integer
d_addr_112 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.StackAddr.in-stack
d_in'45'stack_114 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'stack_114 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_in'45'stack_22 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.frameSlot
d_frameSlot_118 ::
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Maybe Integer
d_frameSlot_118
  = coe
      MAlonzo.Code.Once.Memory.FrameOps.du_frameSlot_32
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.StackGrowth.d_x86'45'stack'45'growth_118)
-- Once.CCC.Target.X86-64.Layout._.stackAddr-write-preserves-code
d_stackAddr'45'write'45'preserves'45'code_120 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stackAddr'45'write'45'preserves'45'code_120 = erased
-- Once.CCC.Target.X86-64.Layout._.stackAddr-write-preserves-heap
d_stackAddr'45'write'45'preserves'45'heap_122 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stackAddr'45'write'45'preserves'45'heap_122 = erased
-- Once.CCC.Target.X86-64.Layout._.FrameSlotInternal.frameSlot-is-readMem
d_frameSlot'45'is'45'readMem_126 ::
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frameSlot'45'is'45'readMem_126 = erased
-- Once.CCC.Target.X86-64.Layout._.FrameSlotInternal.init-frame-slot-at-base
d_init'45'frame'45'slot'45'at'45'base_128 ::
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45'frame'45'slot'45'at'45'base_128 = erased
-- Once.CCC.Target.X86-64.Layout.x86-stack-lower-zero
d_x86'45'stack'45'lower'45'zero_130 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'stack'45'lower'45'zero_130 = erased
-- Once.CCC.Target.X86-64.Layout.x86-code-lower-zero
d_x86'45'code'45'lower'45'zero_132 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'code'45'lower'45'zero_132 = erased
-- Once.CCC.Target.X86-64.Layout.prog-fits-in-code
d_prog'45'fits'45'in'45'code_136 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_prog'45'fits'45'in'45'code_136
  = coe
      MAlonzo.Code.Once.Memory.RuntimeContract.d_prog'45'fits_54
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.RuntimeParams.d_x86'45'64'45'runtime_10)
-- Once.CCC.Target.X86-64.Layout.pc-in-code
d_pc'45'in'45'code_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pc'45'in'45'code_142 ~v0 v1 v2 = du_pc'45'in'45'code_142 v1 v2
du_pc'45'in'45'code_142 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pc'45'in'45'code_142 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (coe du_pc'8804'upper_154 (coe v0) (coe v1))
-- Once.CCC.Target.X86-64.Layout._.pc≤upper
d_pc'8804'upper_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pc'8804'upper_154 ~v0 v1 v2 = du_pc'8804'upper_154 v1 v2
du_pc'8804'upper_154 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pc'8804'upper_154 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v1))
      (coe d_prog'45'fits'45'in'45'code_136 v0)
-- Once.CCC.Target.X86-64.Layout.stack-sub-preserves
d_stack'45'sub'45'preserves_160 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'sub'45'preserves_160 v0 v1 v2 ~v3
  = du_stack'45'sub'45'preserves_160 v0 v1 v2
du_stack'45'sub'45'preserves_160 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'sub'45'preserves_160 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             (coe du_a'8760'k'8804'upper_176 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Layout._.a∸k≤upper
d_a'8760'k'8804'upper_176 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'8760'k'8804'upper_176 v0 v1 ~v2 v3 ~v4
  = du_a'8760'k'8804'upper_176 v0 v1 v3
du_a'8760'k'8804'upper_176 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'8760'k'8804'upper_176 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184 (coe v0)
         (coe v1))
      (coe v2)
-- Once.CCC.Target.X86-64.Layout.stack-sub-preserves'
d_stack'45'sub'45'preserves''_182 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'sub'45'preserves''_182 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                (coe
                   MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184 (coe v0)
                   (coe v1))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.Layout.slot-addr-≥-base
d_slot'45'addr'45''8805''45'base_196 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'addr'45''8805''45'base_196 v0 ~v1
  = du_slot'45'addr'45''8805''45'base_196 v0
du_slot'45'addr'45''8805''45'base_196 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'addr'45''8805''45'base_196 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
-- Once.CCC.Target.X86-64.Layout.slot-addr-next-is-base-plus-word
d_slot'45'addr'45'next'45'is'45'base'45'plus'45'word_204 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'next'45'is'45'base'45'plus'45'word_204 = erased
-- Once.CCC.Target.X86-64.Layout.frame-below-slot0-disjoint
d_frame'45'below'45'slot0'45'disjoint_214 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'below'45'slot0'45'disjoint_214 = erased
-- Once.CCC.Target.X86-64.Layout._.slot0-eq
d_slot0'45'eq_230 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot0'45'eq_230 = erased
-- Once.CCC.Target.X86-64.Layout._.slot-k-≥-frame2
d_slot'45'k'45''8805''45'frame2_232 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'k'45''8805''45'frame2_232 ~v0 v1 ~v2 ~v3 ~v4
  = du_slot'45'k'45''8805''45'frame2_232 v1
du_slot'45'k'45''8805''45'frame2_232 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'k'45''8805''45'frame2_232 v0
  = coe du_slot'45'addr'45''8805''45'base_196 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.slot0<slot-k
d_slot0'60'slot'45'k_234 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot0'60'slot'45'k_234 ~v0 v1 ~v2 v3 ~v4
  = du_slot0'60'slot'45'k_234 v1 v3
du_slot0'60'slot'45'k_234 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot0'60'slot'45'k_234 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v1) (coe du_slot'45'k'45''8805''45'frame2_232 (coe v0))
-- Once.CCC.Target.X86-64.Layout._.slot0≡slot-k
d_slot0'8801'slot'45'k_238 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot0'8801'slot'45'k_238 = erased
-- Once.CCC.Target.X86-64.Layout.frame-preserved-slot0-disjoint
d_frame'45'preserved'45'slot0'45'disjoint_246 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'preserved'45'slot0'45'disjoint_246 = erased
-- Once.CCC.Target.X86-64.Layout._.word-size>0
d_word'45'size'62'0_260 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_word'45'size'62'0_260 ~v0 ~v1 ~v2 ~v3 = du_word'45'size'62'0_260
du_word'45'size'62'0_260 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_word'45'size'62'0_260
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.CCC.Target.X86-64.Layout._.frame1<frame1+8
d_frame1'60'frame1'43'8_262 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame1'60'frame1'43'8_262 v0 ~v1 ~v2 ~v3
  = du_frame1'60'frame1'43'8_262 v0
du_frame1'60'frame1'43'8_262 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_frame1'60'frame1'43'8_262 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe du_word'45'size'62'0_260)
-- Once.CCC.Target.X86-64.Layout._.frame1<frame2
d_frame1'60'frame2_264 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_frame1'60'frame2_264 v0 ~v1 ~v2 v3
  = du_frame1'60'frame2_264 v0 v3
du_frame1'60'frame2_264 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_frame1'60'frame2_264 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe du_frame1'60'frame1'43'8_262 (coe v0)) (coe v1)
-- Once.CCC.Target.X86-64.Layout.slot-addr-above-thunk-rbp
d_slot'45'addr'45'above'45'thunk'45'rbp_274 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'addr'45'above'45'thunk'45'rbp_274 ~v0 ~v1 v2 ~v3 ~v4 ~v5
                                            ~v6
  = du_slot'45'addr'45'above'45'thunk'45'rbp_274 v2
du_slot'45'addr'45'above'45'thunk'45'rbp_274 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'addr'45'above'45'thunk'45'rbp_274 v0
  = coe du_slot'62'rbp_308 (coe v0)
-- Once.CCC.Target.X86-64.Layout._.slot-eq
d_slot'45'eq_294 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'eq_294 = erased
-- Once.CCC.Target.X86-64.Layout._.slot≥rsp+8
d_slot'8805'rsp'43'8_298 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'8805'rsp'43'8_298 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_slot'8805'rsp'43'8_298 v2
du_slot'8805'rsp'43'8_298 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'8805'rsp'43'8_298 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
      (coe addInt (coe (8 :: Integer)) (coe v0))
-- Once.CCC.Target.X86-64.Layout._.rsp+8>rsp
d_rsp'43'8'62'rsp_302 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rsp'43'8'62'rsp_302 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_rsp'43'8'62'rsp_302 v2
du_rsp'43'8'62'rsp_302 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rsp'43'8'62'rsp_302 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Once.CCC.Target.X86-64.Layout._.rbp≤rsp
d_rbp'8804'rsp_304 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rbp'8804'rsp_304 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_rbp'8804'rsp_304 v2
du_rbp'8804'rsp_304 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rbp'8804'rsp_304 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184 (coe v0)
      (coe (16 :: Integer))
-- Once.CCC.Target.X86-64.Layout._.slot>rbp
d_slot'62'rbp_308 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'62'rbp_308 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_slot'62'rbp_308 v2
du_slot'62'rbp_308 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'62'rbp_308 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
      (coe du_rbp'8804'rsp_304 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
         (coe du_rsp'43'8'62'rsp_302 (coe v0))
         (coe du_slot'8805'rsp'43'8_298 (coe v0)))
-- Once.CCC.Target.X86-64.Layout.init-frame-slot-at-base
d_init'45'frame'45'slot'45'at'45'base_314 ::
  (Integer -> Maybe Integer) ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_init'45'frame'45'slot'45'at'45'base_314 = erased
