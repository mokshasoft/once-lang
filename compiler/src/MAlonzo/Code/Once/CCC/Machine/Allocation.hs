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
d_stack'45'alloc_48 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_48 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-loc
d_stack'45'alloc'45'loc_58 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_58 v0 ~v1 = du_stack'45'alloc'45'loc_58 v0
du_stack'45'alloc'45'loc_58 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-state
d_stack'45'alloc'45'state_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_stack'45'alloc'45'state_68 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_80 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_80 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_80 v0
du_stack'45'alloc'45'in'45'frame_80 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_80 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-offset
d_stack'45'alloc'45'offset_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_92 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_92 v0 v2
du_stack'45'alloc'45'offset_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_92 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc
d_heap'45'alloc_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_110 v0 ~v1 = du_heap'45'alloc_110 v0
du_heap'45'alloc_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_110 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-hl
d_heap'45'alloc'45'hl_120 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_120 v0 ~v1 = du_heap'45'alloc'45'hl_120 v0
du_heap'45'alloc'45'hl_120 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_120 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-loc
d_heap'45'alloc'45'loc_130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_130 v0 ~v1 = du_heap'45'alloc'45'loc_130 v0
du_heap'45'alloc'45'loc_130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_130 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-state
d_heap'45'alloc'45'state_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_heap'45'alloc'45'state_140 v0 ~v1
  = du_heap'45'alloc'45'state_140 v0
du_heap'45'alloc'45'state_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_heap'45'alloc'45'state_140 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc
d_stack'45'alloc_152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_152 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_154 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_154 v0
du_stack'45'alloc'45'in'45'frame_154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_154 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-loc
d_stack'45'alloc'45'loc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_156 v0 ~v1
  = du_stack'45'alloc'45'loc_156 v0
du_stack'45'alloc'45'loc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_156 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-offset
d_stack'45'alloc'45'offset_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_158 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_158 v0 v2
du_stack'45'alloc'45'offset_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_158 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-state
d_stack'45'alloc'45'state_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_stack'45'alloc'45'state_160 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc
d_heap'45'alloc_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_164 v0 ~v1 = du_heap'45'alloc_164 v0
du_heap'45'alloc_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_164 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-hl
d_heap'45'alloc'45'hl_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_166 v0 ~v1 = du_heap'45'alloc'45'hl_166 v0
du_heap'45'alloc'45'hl_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_166 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-loc
d_heap'45'alloc'45'loc_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_168 v0 ~v1 = du_heap'45'alloc'45'loc_168 v0
du_heap'45'alloc'45'loc_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-state
d_heap'45'alloc'45'state_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_heap'45'alloc'45'state_170 v0 ~v1
  = du_heap'45'alloc'45'state_170 v0
du_heap'45'alloc'45'state_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_heap'45'alloc'45'state_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator.AllocResult
d_AllocResult_176 a0 a1 a2 = ()
data T_AllocResult_176
  = C_constructor_190 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.location
d_location_186 ::
  T_AllocResult_176 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_location_186 v0
  = case coe v0 of
      C_constructor_190 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.new-state
d_new'45'state_188 ::
  T_AllocResult_176 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_new'45'state_188 v0
  = case coe v0 of
      C_constructor_190 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.alloc-stack
d_alloc'45'stack_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> T_AllocResult_176
d_alloc'45'stack_196 ~v0 v1 v2 = du_alloc'45'stack_196 v1 v2
du_alloc'45'stack_196 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> T_AllocResult_176
du_alloc'45'stack_196 v0 v1
  = coe
      C_constructor_190
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.alloc-heap
d_alloc'45'heap_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> T_AllocResult_176
d_alloc'45'heap_206 ~v0 v1 ~v2 = du_alloc'45'heap_206 v1
du_alloc'45'heap_206 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  T_AllocResult_176
du_alloc'45'heap_206 v0
  = coe
      C_constructor_190
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0)))
-- Once.CCC.Machine.Allocation.LocStateWithAlloc
d_LocStateWithAlloc_214 a0 = ()
data T_LocStateWithAlloc_214
  = C_mkLocStateWithAlloc_226 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
                              MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.machine-state
d_machine'45'state_222 ::
  T_LocStateWithAlloc_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_machine'45'state_222 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_226 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.alloc-state
d_alloc'45'state_224 ::
  T_LocStateWithAlloc_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_alloc'45'state_224 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_226 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-slot
d_write'45'stack'45'slot_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_write'45'stack'45'slot_306 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_740 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 (coe v1))
         (coe v2) (coe v3) (coe v4))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v1))
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-slot
d_write'45'heap'45'slot_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_write'45'heap'45'slot_316 ~v0 v1 v2 v3
  = du_write'45'heap'45'slot_316 v1 v2 v3
du_write'45'heap'45'slot_316 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_write'45'heap'45'slot_316 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_850
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 (coe v0))
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v0))
-- Once.CCC.Machine.Allocation.WriteOps.write-loc
d_write'45'loc_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_write'45'loc_324 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_write'45'stack'45'slot_306 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_write'45'heap'45'slot_316 (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-preserves-diff
d_write'45'stack'45'preserves'45'diff_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'preserves'45'diff_356 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-read-same
d_write'45'stack'45'read'45'same_472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'read'45'same_472 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-read-same
d_write'45'heap'45'read'45'same_520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'heap'45'read'45'same_520 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_626 a0 a1 a2 a3 a4 = ()
data T_StackAncestorSource_626
  = C_src'45'origin_634 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_src'45'above'45'origin_642 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_646 a0 a1 a2 = ()
data T_BeforeFrontier_646
  = C_stack'45'before_654 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_stack'45'ancestor_664 AgdaAny Integer AgdaAny
                            T_StackAncestorSource_626 |
    C_heap'45'before_668 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_674 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_686 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_646 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_746 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_stack'45'alloc'45'advances_780 ~v0 v1 ~v2 v3 v4
  = du_stack'45'alloc'45'advances_780 v1 v3 v4
du_stack'45'alloc'45'advances_780 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_stack'45'alloc'45'advances_780 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_654 v8
               -> coe
                    C_stack'45'before_654
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v8)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))))
             C_stack'45'ancestor_664 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_664 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_668 v5 -> coe C_heap'45'before_668 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_heap'45'alloc'45'advances_816 ~v0 v1 v2 v3
  = du_heap'45'alloc'45'advances_816 v1 v2 v3
du_heap'45'alloc'45'advances_816 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_heap'45'alloc'45'advances_816 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_654 v8 -> coe C_stack'45'before_654 v8
             C_stack'45'ancestor_664 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_664 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_668 v5
               -> coe
                    C_heap'45'before_668
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v5)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                             (coe v0))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_frontier'45'monotone_850 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_frontier'45'monotone_850 v4 v5 v6 v7
du_frontier'45'monotone_850 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_frontier'45'monotone_850 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> case coe v3 of
             C_stack'45'before_654 v9
               -> coe
                    C_stack'45'before_654
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v9) (coe v0))
             C_stack'45'ancestor_664 v8 v9 v10 v11
               -> coe C_stack'45'ancestor_664 v8 v9 v10 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_heap'45'before_668 v6
               -> coe
                    C_heap'45'before_668
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v6) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump
d_AllocBump_912 a0 = ()
data T_AllocBump_912 = C_mkBump_922 Integer Integer
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_918 :: T_AllocBump_912 -> Integer
d_next'45'slot'45'delta_918 v0
  = case coe v0 of
      C_mkBump_922 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_920 :: T_AllocBump_912 -> Integer
d_next'45'heap'45'ref'45'delta_920 v0
  = case coe v0 of
      C_mkBump_922 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump
d_apply'45'bump_924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_apply'45'bump_924 ~v0 v1 v2 = du_apply'45'bump_924 v1 v2
du_apply'45'bump_924 ::
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_apply'45'bump_924 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v1))
      (coe
         addInt (coe d_next'45'slot'45'delta_918 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_920 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v1))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-0
d_bump'45'0_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912
d_bump'45'0_930 ~v0 = du_bump'45'0_930
du_bump'45'0_930 :: T_AllocBump_912
du_bump'45'0_930
  = coe C_mkBump_922 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-+
d_bump'45''43'_932 ::
  T_AllocBump_912 -> T_AllocBump_912 -> T_AllocBump_912
d_bump'45''43'_932 v0 v1
  = coe
      C_mkBump_922
      (coe
         addInt (coe d_next'45'slot'45'delta_918 (coe v0))
         (coe d_next'45'slot'45'delta_918 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_920 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_920 (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_942 ::
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_942 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912 ->
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_950 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant._.compose-eq
d_compose'45'eq_968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912 ->
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'eq_968 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_984 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_984 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump
d_AllocBump_1024 a0 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.BeforeFrontier
d_BeforeFrontier_1028 a0 a1 a2 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.StackAncestorSource
d_StackAncestorSource_1030 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump
d_apply'45'bump_1032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_apply'45'bump_1032 ~v0 = du_apply'45'bump_1032
du_apply'45'bump_1032 ::
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_apply'45'bump_1032 = coe du_apply'45'bump_924
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1034 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1034 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-compose
d_apply'45'bump'45'compose_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912 ->
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_1036 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_1038 ::
  T_AllocBump_912 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_1038 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_646 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_1040 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.bump-+
d_bump'45''43'_1042 ::
  T_AllocBump_912 -> T_AllocBump_912 -> T_AllocBump_912
d_bump'45''43'_1042 v0 v1
  = coe
      C_mkBump_922
      (coe
         addInt (coe d_next'45'slot'45'delta_918 (coe v0))
         (coe d_next'45'slot'45'delta_918 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_920 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_920 (coe v1)))
-- Once.CCC.Machine.Allocation.FrameOps._.bump-0
d_bump'45'0_1044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_912
d_bump'45'0_1044 ~v0 = du_bump'45'0_1044
du_bump'45'0_1044 :: T_AllocBump_912
du_bump'45'0_1044 = coe du_bump'45'0_930
-- Once.CCC.Machine.Allocation.FrameOps._.fresh-stack-after
d_fresh'45'stack'45'after_1046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1046 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.frontier-monotone
d_frontier'45'monotone_1048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_frontier'45'monotone_1048 ~v0 = du_frontier'45'monotone_1048
du_frontier'45'monotone_1048 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_frontier'45'monotone_1048 v0 v1 v2 v3 v4 v5 v6
  = coe du_frontier'45'monotone_850 v3 v4 v5 v6
-- Once.CCC.Machine.Allocation.FrameOps._.heap-alloc-advances
d_heap'45'alloc'45'advances_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_heap'45'alloc'45'advances_1050 ~v0
  = du_heap'45'alloc'45'advances_1050
du_heap'45'alloc'45'advances_1050 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_heap'45'alloc'45'advances_1050
  = coe du_heap'45'alloc'45'advances_816
-- Once.CCC.Machine.Allocation.FrameOps._.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1056 :: T_AllocBump_912 -> Integer
d_next'45'heap'45'ref'45'delta_1056 v0
  = coe d_next'45'heap'45'ref'45'delta_920 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.next-slot-delta
d_next'45'slot'45'delta_1058 :: T_AllocBump_912 -> Integer
d_next'45'slot'45'delta_1058 v0
  = coe d_next'45'slot'45'delta_918 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.stack-alloc-advances
d_stack'45'alloc'45'advances_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_stack'45'alloc'45'advances_1064 ~v0
  = du_stack'45'alloc'45'advances_1064
du_stack'45'alloc'45'advances_1064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_stack'45'alloc'45'advances_1064 v0 v1 v2 v3
  = coe du_stack'45'alloc'45'advances_780 v0 v2 v3
-- Once.CCC.Machine.Allocation.FrameOps._.≺⇒≢
d_'8826''8658''8802'_1070 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1070 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1074 :: T_AllocBump_912 -> Integer
d_next'45'heap'45'ref'45'delta_1074 v0
  = coe d_next'45'heap'45'ref'45'delta_920 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1076 :: T_AllocBump_912 -> Integer
d_next'45'slot'45'delta_1076 v0
  = coe d_next'45'slot'45'delta_918 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps.push-frame
d_push'45'frame_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_push'45'frame_1098 ~v0 v1 v2 v3 = du_push'45'frame_1098 v1 v2 v3
du_push'45'frame_1098 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_push'45'frame_1098 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
               (coe v0))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v0)))
      (coe v2) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.pop-frame
d_pop'45'frame_1112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_pop'45'frame_1112 ~v0 v1 v2 v3 = du_pop'45'frame_1112 v1 v2 v3
du_pop'45'frame_1112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_pop'45'frame_1112 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.in-parent-frame-before-child
d_in'45'parent'45'frame'45'before'45'child_1128 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
d_in'45'parent'45'frame'45'before'45'child_1128 v0 ~v1 ~v2 ~v3 v4
                                                v5
  = du_in'45'parent'45'frame'45'before'45'child_1128 v0 v4 v5
du_in'45'parent'45'frame'45'before'45'child_1128 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
du_in'45'parent'45'frame'45'before'45'child_1128 v0 v1 v2
  = coe
      C_stack'45'ancestor_664
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v0))
      v1 (coe C_src'45'origin_634 v2)
-- Once.CCC.Machine.Allocation.FrameOps.heap-before-child
d_heap'45'before'45'child_1150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
d_heap'45'before'45'child_1150 ~v0 ~v1 ~v2 ~v3 v4
  = du_heap'45'before'45'child_1150 v4
du_heap'45'before'45'child_1150 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
du_heap'45'before'45'child_1150 v0 = coe C_heap'45'before_668 v0
-- Once.CCC.Machine.Allocation.FrameOps.ancestor-frame-before-child
d_ancestor'45'frame'45'before'45'child_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_646
d_ancestor'45'frame'45'before'45'child_1176 v0 v1 v2 ~v3 v4 ~v5 v6
                                            v7 v8 v9
  = du_ancestor'45'frame'45'before'45'child_1176
      v0 v1 v2 v4 v6 v7 v8 v9
du_ancestor'45'frame'45'before'45'child_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_646
du_ancestor'45'frame'45'before'45'child_1176 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      C_stack'45'ancestor_664
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
         (coe v1))
      v4
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_126 v0 v2
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v1))
         v3 v6 v7)
      (coe C_src'45'above'45'origin_642 v7 v5)
-- Once.CCC.Machine.Allocation.FrameOps.parent-before-child
d_parent'45'before'45'child_1204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_646 -> T_BeforeFrontier_646
d_parent'45'before'45'child_1204 v0 v1 v2 ~v3 v4 v5 v6
  = du_parent'45'before'45'child_1204 v0 v1 v2 v4 v5 v6
du_parent'45'before'45'child_1204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_646 -> T_BeforeFrontier_646
du_parent'45'before'45'child_1204 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
        -> case coe v5 of
             C_stack'45'before_654 v11
               -> coe
                    C_stack'45'ancestor_664
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                       (coe v1))
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v1))
                    v4 (coe C_src'45'origin_634 v11)
             C_stack'45'ancestor_664 v10 v11 v12 v13
               -> case coe v13 of
                    C_src'45'origin_634 v16
                      -> coe
                           C_stack'45'ancestor_664
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_126 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_642 v12 v16)
                    C_src'45'above'45'origin_642 v16 v18
                      -> coe
                           C_stack'45'ancestor_664
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_126 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_642 v12 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
        -> case coe v5 of
             C_heap'45'before_668 v8 -> coe C_heap'45'before_668 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrameOps.pop-preserves-before
d_pop'45'preserves'45'before_1276 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
d_pop'45'preserves'45'before_1276 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'preserves'45'before_1276 v4
du_pop'45'preserves'45'before_1276 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
du_pop'45'preserves'45'before_1276 v0
  = coe C_stack'45'before_654 v0
-- Once.CCC.Machine.Allocation.FrameOps.pop-heap-before
d_pop'45'heap'45'before_1296 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
d_pop'45'heap'45'before_1296 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'heap'45'before_1296 v4
du_pop'45'heap'45'before_1296 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_646
du_pop'45'heap'45'before_1296 v0 = coe C_heap'45'before_668 v0
