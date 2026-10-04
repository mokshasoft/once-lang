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

module MAlonzo.Code.Once.CCC.Machine.Allocation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress

-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc
d_stack'45'alloc_54 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_54 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-loc
d_stack'45'alloc'45'loc_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_64 v0 ~v1 = du_stack'45'alloc'45'loc_64 v0
du_stack'45'alloc'45'loc_64 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_64 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-state
d_stack'45'alloc'45'state_74 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_stack'45'alloc'45'state_74 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_86 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_86 v0
du_stack'45'alloc'45'in'45'frame_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_86 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-offset
d_stack'45'alloc'45'offset_98 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_98 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_98 v0 v2
du_stack'45'alloc'45'offset_98 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_98 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc
d_heap'45'alloc_116 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_116 v0 ~v1 = du_heap'45'alloc_116 v0
du_heap'45'alloc_116 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_116 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-hl
d_heap'45'alloc'45'hl_126 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_126 v0 ~v1 = du_heap'45'alloc'45'hl_126 v0
du_heap'45'alloc'45'hl_126 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_126 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-loc
d_heap'45'alloc'45'loc_136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_136 v0 ~v1 = du_heap'45'alloc'45'loc_136 v0
du_heap'45'alloc'45'loc_136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_136 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-state
d_heap'45'alloc'45'state_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_heap'45'alloc'45'state_146 v0 ~v1
  = du_heap'45'alloc'45'state_146 v0
du_heap'45'alloc'45'state_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_heap'45'alloc'45'state_146 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc
d_stack'45'alloc_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_158 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_160 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_160 v0
du_stack'45'alloc'45'in'45'frame_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_160 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-loc
d_stack'45'alloc'45'loc_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_162 v0 ~v1
  = du_stack'45'alloc'45'loc_162 v0
du_stack'45'alloc'45'loc_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_162 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-offset
d_stack'45'alloc'45'offset_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_164 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_164 v0 v2
du_stack'45'alloc'45'offset_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_164 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-state
d_stack'45'alloc'45'state_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_stack'45'alloc'45'state_166 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc
d_heap'45'alloc_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_170 v0 ~v1 = du_heap'45'alloc_170 v0
du_heap'45'alloc_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_170 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-hl
d_heap'45'alloc'45'hl_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_172 v0 ~v1 = du_heap'45'alloc'45'hl_172 v0
du_heap'45'alloc'45'hl_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_172 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-loc
d_heap'45'alloc'45'loc_174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_174 v0 ~v1 = du_heap'45'alloc'45'loc_174 v0
du_heap'45'alloc'45'loc_174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-state
d_heap'45'alloc'45'state_176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_heap'45'alloc'45'state_176 v0 ~v1
  = du_heap'45'alloc'45'state_176 v0
du_heap'45'alloc'45'state_176 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_heap'45'alloc'45'state_176 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator.AllocResult
d_AllocResult_182 a0 a1 a2 = ()
data T_AllocResult_182
  = C_constructor_196 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.location
d_location_192 ::
  T_AllocResult_182 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_location_192 v0
  = case coe v0 of
      C_constructor_196 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.new-state
d_new'45'state_194 ::
  T_AllocResult_182 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_new'45'state_194 v0
  = case coe v0 of
      C_constructor_196 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.alloc-stack
d_alloc'45'stack_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> T_AllocResult_182
d_alloc'45'stack_202 ~v0 v1 v2 = du_alloc'45'stack_202 v1 v2
du_alloc'45'stack_202 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> T_AllocResult_182
du_alloc'45'stack_202 v0 v1
  = coe
      C_constructor_196
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.alloc-heap
d_alloc'45'heap_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> T_AllocResult_182
d_alloc'45'heap_212 ~v0 v1 ~v2 = du_alloc'45'heap_212 v1
du_alloc'45'heap_212 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  T_AllocResult_182
du_alloc'45'heap_212 v0
  = coe
      C_constructor_196
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0)))
-- Once.CCC.Machine.Allocation.LocStateWithAlloc
d_LocStateWithAlloc_220 a0 = ()
data T_LocStateWithAlloc_220
  = C_mkLocStateWithAlloc_232 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
                              MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.machine-state
d_machine'45'state_228 ::
  T_LocStateWithAlloc_220 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_machine'45'state_228 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_232 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.alloc-state
d_alloc'45'state_230 ::
  T_LocStateWithAlloc_220 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_alloc'45'state_230 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_232 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-slot
d_write'45'stack'45'slot_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_write'45'stack'45'slot_318 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_436
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_694 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428 (coe v1))
         (coe v2) (coe v3) (coe v4))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_430 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_432 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434 (coe v1))
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-slot
d_write'45'heap'45'slot_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_write'45'heap'45'slot_328 ~v0 v1 v2 v3
  = du_write'45'heap'45'slot_328 v1 v2 v3
du_write'45'heap'45'slot_328 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
du_write'45'heap'45'slot_328 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_436
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_426 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_428 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_804
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_430 (coe v0))
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_432 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_434 (coe v0))
-- Once.CCC.Machine.Allocation.WriteOps.write-loc
d_write'45'loc_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412
d_write'45'loc_336 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_write'45'stack'45'slot_318 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_write'45'heap'45'slot_328 (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-preserves-diff
d_write'45'stack'45'preserves'45'diff_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'preserves'45'diff_368 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-read-same
d_write'45'stack'45'read'45'same_484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'read'45'same_484 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-read-same
d_write'45'heap'45'read'45'same_532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'heap'45'read'45'same_532 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_644 a0 a1 a2 a3 a4 = ()
data T_StackAncestorSource_644
  = C_src'45'origin_652 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_src'45'above'45'origin_660 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_664 a0 a1 a2 = ()
data T_BeforeFrontier_664
  = C_stack'45'before_672 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_stack'45'ancestor_682 AgdaAny Integer AgdaAny
                            T_StackAncestorSource_644 |
    C_heap'45'before_686 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_692 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_704 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_764 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_stack'45'alloc'45'advances_798 ~v0 v1 ~v2 v3 v4
  = du_stack'45'alloc'45'advances_798 v1 v3 v4
du_stack'45'alloc'45'advances_798 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_stack'45'alloc'45'advances_798 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_672 v8
               -> coe
                    C_stack'45'before_672
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v8)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))))
             C_stack'45'ancestor_682 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_682 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_686 v5 -> coe C_heap'45'before_686 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_heap'45'alloc'45'advances_834 ~v0 v1 v2 v3
  = du_heap'45'alloc'45'advances_834 v1 v2 v3
du_heap'45'alloc'45'advances_834 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_heap'45'alloc'45'advances_834 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_672 v8 -> coe C_stack'45'before_672 v8
             C_stack'45'ancestor_682 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_682 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_686 v5
               -> coe
                    C_heap'45'before_686
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v5)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
                             (coe v0))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_frontier'45'monotone_868 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_frontier'45'monotone_868 v4 v5 v6 v7
du_frontier'45'monotone_868 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_frontier'45'monotone_868 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> case coe v3 of
             C_stack'45'before_672 v9
               -> coe
                    C_stack'45'before_672
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v9) (coe v0))
             C_stack'45'ancestor_682 v8 v9 v10 v11
               -> coe C_stack'45'ancestor_682 v8 v9 v10 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_heap'45'before_686 v6
               -> coe
                    C_heap'45'before_686
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v6) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump
d_AllocBump_930 a0 = ()
data T_AllocBump_930 = C_mkBump_940 Integer Integer
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_936 :: T_AllocBump_930 -> Integer
d_next'45'slot'45'delta_936 v0
  = case coe v0 of
      C_mkBump_940 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_938 :: T_AllocBump_930 -> Integer
d_next'45'heap'45'ref'45'delta_938 v0
  = case coe v0 of
      C_mkBump_940 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump
d_apply'45'bump_942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_apply'45'bump_942 ~v0 v1 v2 = du_apply'45'bump_942 v1 v2
du_apply'45'bump_942 ::
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_apply'45'bump_942 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v1))
      (coe
         addInt (coe d_next'45'slot'45'delta_936 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_938 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v1))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-0
d_bump'45'0_948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930
d_bump'45'0_948 ~v0 = du_bump'45'0_948
du_bump'45'0_948 :: T_AllocBump_930
du_bump'45'0_948
  = coe C_mkBump_940 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-+
d_bump'45''43'_950 ::
  T_AllocBump_930 -> T_AllocBump_930 -> T_AllocBump_930
d_bump'45''43'_950 v0 v1
  = coe
      C_mkBump_940
      (coe
         addInt (coe d_next'45'slot'45'delta_936 (coe v0))
         (coe d_next'45'slot'45'delta_936 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_938 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_938 (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_960 ::
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_960 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930 ->
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_968 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant._.compose-eq
d_compose'45'eq_986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930 ->
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'eq_986 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1002 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1002 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump
d_AllocBump_1048 a0 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.BeforeFrontier
d_BeforeFrontier_1052 a0 a1 a2 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.StackAncestorSource
d_StackAncestorSource_1054 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump
d_apply'45'bump_1056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_apply'45'bump_1056 ~v0 = du_apply'45'bump_1056
du_apply'45'bump_1056 ::
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_apply'45'bump_1056 = coe du_apply'45'bump_942
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1058 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1058 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-compose
d_apply'45'bump'45'compose_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930 ->
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_1060 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_1062 ::
  T_AllocBump_930 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_1062 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_664 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_1064 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.bump-+
d_bump'45''43'_1066 ::
  T_AllocBump_930 -> T_AllocBump_930 -> T_AllocBump_930
d_bump'45''43'_1066 v0 v1
  = coe
      C_mkBump_940
      (coe
         addInt (coe d_next'45'slot'45'delta_936 (coe v0))
         (coe d_next'45'slot'45'delta_936 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_938 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_938 (coe v1)))
-- Once.CCC.Machine.Allocation.FrameOps._.bump-0
d_bump'45'0_1068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_930
d_bump'45'0_1068 ~v0 = du_bump'45'0_1068
du_bump'45'0_1068 :: T_AllocBump_930
du_bump'45'0_1068 = coe du_bump'45'0_948
-- Once.CCC.Machine.Allocation.FrameOps._.fresh-stack-after
d_fresh'45'stack'45'after_1070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1070 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.frontier-monotone
d_frontier'45'monotone_1072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_frontier'45'monotone_1072 ~v0 = du_frontier'45'monotone_1072
du_frontier'45'monotone_1072 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_frontier'45'monotone_1072 v0 v1 v2 v3 v4 v5 v6
  = coe du_frontier'45'monotone_868 v3 v4 v5 v6
-- Once.CCC.Machine.Allocation.FrameOps._.heap-alloc-advances
d_heap'45'alloc'45'advances_1074 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_heap'45'alloc'45'advances_1074 ~v0
  = du_heap'45'alloc'45'advances_1074
du_heap'45'alloc'45'advances_1074 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_heap'45'alloc'45'advances_1074
  = coe du_heap'45'alloc'45'advances_834
-- Once.CCC.Machine.Allocation.FrameOps._.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1080 :: T_AllocBump_930 -> Integer
d_next'45'heap'45'ref'45'delta_1080 v0
  = coe d_next'45'heap'45'ref'45'delta_938 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.next-slot-delta
d_next'45'slot'45'delta_1082 :: T_AllocBump_930 -> Integer
d_next'45'slot'45'delta_1082 v0
  = coe d_next'45'slot'45'delta_936 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.stack-alloc-advances
d_stack'45'alloc'45'advances_1088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_stack'45'alloc'45'advances_1088 ~v0
  = du_stack'45'alloc'45'advances_1088
du_stack'45'alloc'45'advances_1088 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_stack'45'alloc'45'advances_1088 v0 v1 v2 v3
  = coe du_stack'45'alloc'45'advances_798 v0 v2 v3
-- Once.CCC.Machine.Allocation.FrameOps._.≺⇒≢
d_'8826''8658''8802'_1094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1094 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1098 :: T_AllocBump_930 -> Integer
d_next'45'heap'45'ref'45'delta_1098 v0
  = coe d_next'45'heap'45'ref'45'delta_938 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1100 :: T_AllocBump_930 -> Integer
d_next'45'slot'45'delta_1100 v0
  = coe d_next'45'slot'45'delta_936 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps.push-frame
d_push'45'frame_1122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_push'45'frame_1122 ~v0 v1 v2 v3 = du_push'45'frame_1122 v1 v2 v3
du_push'45'frame_1122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_push'45'frame_1122 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
               (coe v0))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
            (coe v0)))
      (coe v2) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.pop-frame
d_pop'45'frame_1136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
d_pop'45'frame_1136 ~v0 v1 v2 v3 = du_pop'45'frame_1136 v1 v2 v3
du_pop'45'frame_1136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504
du_pop'45'frame_1136 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_608
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_598
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_600 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_604
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_606 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.in-parent-frame-before-child
d_in'45'parent'45'frame'45'before'45'child_1152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
d_in'45'parent'45'frame'45'before'45'child_1152 v0 ~v1 ~v2 ~v3 v4
                                                v5
  = du_in'45'parent'45'frame'45'before'45'child_1152 v0 v4 v5
du_in'45'parent'45'frame'45'before'45'child_1152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
du_in'45'parent'45'frame'45'before'45'child_1152 v0 v1 v2
  = coe
      C_stack'45'ancestor_682
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v0))
      v1 (coe C_src'45'origin_652 v2)
-- Once.CCC.Machine.Allocation.FrameOps.heap-before-child
d_heap'45'before'45'child_1174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
d_heap'45'before'45'child_1174 ~v0 ~v1 ~v2 ~v3 v4
  = du_heap'45'before'45'child_1174 v4
du_heap'45'before'45'child_1174 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
du_heap'45'before'45'child_1174 v0 = coe C_heap'45'before_686 v0
-- Once.CCC.Machine.Allocation.FrameOps.ancestor-frame-before-child
d_ancestor'45'frame'45'before'45'child_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_664
d_ancestor'45'frame'45'before'45'child_1200 v0 v1 v2 ~v3 v4 ~v5 v6
                                            v7 v8 v9
  = du_ancestor'45'frame'45'before'45'child_1200
      v0 v1 v2 v4 v6 v7 v8 v9
du_ancestor'45'frame'45'before'45'child_1200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_664
du_ancestor'45'frame'45'before'45'child_1200 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      C_stack'45'ancestor_682
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
         (coe v1))
      v4
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 v0 v2
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
            (coe v1))
         v3 v6 v7)
      (coe C_src'45'above'45'origin_660 v7 v5)
-- Once.CCC.Machine.Allocation.FrameOps.parent-before-child
d_parent'45'before'45'child_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_664 -> T_BeforeFrontier_664
d_parent'45'before'45'child_1228 v0 v1 v2 ~v3 v4 v5 v6
  = du_parent'45'before'45'child_1228 v0 v1 v2 v4 v5 v6
du_parent'45'before'45'child_1228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_664 -> T_BeforeFrontier_664
du_parent'45'before'45'child_1228 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
        -> case coe v5 of
             C_stack'45'before_672 v11
               -> coe
                    C_stack'45'ancestor_682
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                       (coe v1))
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_602 (coe v1))
                    v4 (coe C_src'45'origin_652 v11)
             C_stack'45'ancestor_682 v10 v11 v12 v13
               -> case coe v13 of
                    C_src'45'origin_652 v16
                      -> coe
                           C_stack'45'ancestor_682
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_660 v12 v16)
                    C_src'45'above'45'origin_660 v16 v18
                      -> coe
                           C_stack'45'ancestor_682
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_138 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_596
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_660 v12 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
        -> case coe v5 of
             C_heap'45'before_686 v8 -> coe C_heap'45'before_686 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrameOps.pop-preserves-before
d_pop'45'preserves'45'before_1300 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
d_pop'45'preserves'45'before_1300 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'preserves'45'before_1300 v4
du_pop'45'preserves'45'before_1300 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
du_pop'45'preserves'45'before_1300 v0
  = coe C_stack'45'before_672 v0
-- Once.CCC.Machine.Allocation.FrameOps.pop-heap-before
d_pop'45'heap'45'before_1320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
d_pop'45'heap'45'before_1320 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'heap'45'before_1320 v4
du_pop'45'heap'45'before_1320 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_664
du_pop'45'heap'45'before_1320 v0 = coe C_heap'45'before_686 v0
