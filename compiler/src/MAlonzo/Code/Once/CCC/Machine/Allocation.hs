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
d_stack'45'alloc_52 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_52 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-loc
d_stack'45'alloc'45'loc_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_62 v0 ~v1 = du_stack'45'alloc'45'loc_62 v0
du_stack'45'alloc'45'loc_62 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_62 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-state
d_stack'45'alloc'45'state_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_stack'45'alloc'45'state_72 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_84 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_84 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_84 v0
du_stack'45'alloc'45'in'45'frame_84 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_84 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-offset
d_stack'45'alloc'45'offset_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_96 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_96 v0 v2
du_stack'45'alloc'45'offset_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_96 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc
d_heap'45'alloc_114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_114 v0 ~v1 = du_heap'45'alloc_114 v0
du_heap'45'alloc_114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_114 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-hl
d_heap'45'alloc'45'hl_124 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_124 v0 ~v1 = du_heap'45'alloc'45'hl_124 v0
du_heap'45'alloc'45'hl_124 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_124 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-loc
d_heap'45'alloc'45'loc_134 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_134 v0 ~v1 = du_heap'45'alloc'45'loc_134 v0
du_heap'45'alloc'45'loc_134 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_134 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-state
d_heap'45'alloc'45'state_144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_heap'45'alloc'45'state_144 v0 ~v1
  = du_heap'45'alloc'45'state_144 v0
du_heap'45'alloc'45'state_144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_heap'45'alloc'45'state_144 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc
d_stack'45'alloc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_156 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_158 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_158 v0
du_stack'45'alloc'45'in'45'frame_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_158 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-loc
d_stack'45'alloc'45'loc_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_160 v0 ~v1
  = du_stack'45'alloc'45'loc_160 v0
du_stack'45'alloc'45'loc_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-offset
d_stack'45'alloc'45'offset_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_162 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_162 v0 v2
du_stack'45'alloc'45'offset_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_162 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-state
d_stack'45'alloc'45'state_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_stack'45'alloc'45'state_164 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc
d_heap'45'alloc_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_168 v0 ~v1 = du_heap'45'alloc_168 v0
du_heap'45'alloc_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_168 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-hl
d_heap'45'alloc'45'hl_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_170 v0 ~v1 = du_heap'45'alloc'45'hl_170 v0
du_heap'45'alloc'45'hl_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_170 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-loc
d_heap'45'alloc'45'loc_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_172 v0 ~v1 = du_heap'45'alloc'45'loc_172 v0
du_heap'45'alloc'45'loc_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-state
d_heap'45'alloc'45'state_174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_heap'45'alloc'45'state_174 v0 ~v1
  = du_heap'45'alloc'45'state_174 v0
du_heap'45'alloc'45'state_174 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_heap'45'alloc'45'state_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator.AllocResult
d_AllocResult_180 a0 a1 a2 = ()
data T_AllocResult_180
  = C_constructor_194 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.location
d_location_190 ::
  T_AllocResult_180 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_location_190 v0
  = case coe v0 of
      C_constructor_194 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.new-state
d_new'45'state_192 ::
  T_AllocResult_180 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_new'45'state_192 v0
  = case coe v0 of
      C_constructor_194 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.alloc-stack
d_alloc'45'stack_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_AllocResult_180
d_alloc'45'stack_200 ~v0 v1 v2 = du_alloc'45'stack_200 v1 v2
du_alloc'45'stack_200 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_AllocResult_180
du_alloc'45'stack_200 v0 v1
  = coe
      C_constructor_194
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.alloc-heap
d_alloc'45'heap_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_AllocResult_180
d_alloc'45'heap_210 ~v0 v1 ~v2 = du_alloc'45'heap_210 v1
du_alloc'45'heap_210 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_AllocResult_180
du_alloc'45'heap_210 v0
  = coe
      C_constructor_194
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0)))
-- Once.CCC.Machine.Allocation.LocStateWithAlloc
d_LocStateWithAlloc_218 a0 = ()
data T_LocStateWithAlloc_218
  = C_mkLocStateWithAlloc_230 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
                              MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.machine-state
d_machine'45'state_226 ::
  T_LocStateWithAlloc_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_machine'45'state_226 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_230 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.alloc-state
d_alloc'45'state_228 ::
  T_LocStateWithAlloc_218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_alloc'45'state_228 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_230 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-slot
d_write'45'stack'45'slot_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'stack'45'slot_314 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_672 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 (coe v1))
         (coe v2) (coe v3) (coe v4))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v1))
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-slot
d_write'45'heap'45'slot_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'heap'45'slot_324 ~v0 v1 v2 v3
  = du_write'45'heap'45'slot_324 v1 v2 v3
du_write'45'heap'45'slot_324 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_write'45'heap'45'slot_324 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_782
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 (coe v0))
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v0))
-- Once.CCC.Machine.Allocation.WriteOps.write-loc
d_write'45'loc_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'loc_332 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_write'45'stack'45'slot_314 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_write'45'heap'45'slot_324 (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-preserves-diff
d_write'45'stack'45'preserves'45'diff_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'preserves'45'diff_364 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-read-same
d_write'45'stack'45'read'45'same_480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'read'45'same_480 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-read-same
d_write'45'heap'45'read'45'same_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'heap'45'read'45'same_528 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_638 a0 a1 a2 a3 a4 = ()
data T_StackAncestorSource_638
  = C_src'45'origin_646 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_src'45'above'45'origin_654 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_658 a0 a1 a2 = ()
data T_BeforeFrontier_658
  = C_stack'45'before_666 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_stack'45'ancestor_676 AgdaAny Integer AgdaAny
                            T_StackAncestorSource_638 |
    C_heap'45'before_680 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_686 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_698 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_758 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_stack'45'alloc'45'advances_792 ~v0 v1 ~v2 v3 v4
  = du_stack'45'alloc'45'advances_792 v1 v3 v4
du_stack'45'alloc'45'advances_792 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_stack'45'alloc'45'advances_792 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_666 v8
               -> coe
                    C_stack'45'before_666
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v8)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))))
             C_stack'45'ancestor_676 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_676 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_680 v5 -> coe C_heap'45'before_680 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_heap'45'alloc'45'advances_828 ~v0 v1 v2 v3
  = du_heap'45'alloc'45'advances_828 v1 v2 v3
du_heap'45'alloc'45'advances_828 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_heap'45'alloc'45'advances_828 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_666 v8 -> coe C_stack'45'before_666 v8
             C_stack'45'ancestor_676 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_676 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_680 v5
               -> coe
                    C_heap'45'before_680
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v5)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                             (coe v0))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_frontier'45'monotone_862 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_frontier'45'monotone_862 v4 v5 v6 v7
du_frontier'45'monotone_862 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_frontier'45'monotone_862 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> case coe v3 of
             C_stack'45'before_666 v9
               -> coe
                    C_stack'45'before_666
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v9) (coe v0))
             C_stack'45'ancestor_676 v8 v9 v10 v11
               -> coe C_stack'45'ancestor_676 v8 v9 v10 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_heap'45'before_680 v6
               -> coe
                    C_heap'45'before_680
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v6) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump
d_AllocBump_924 a0 = ()
data T_AllocBump_924 = C_mkBump_934 Integer Integer
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_930 :: T_AllocBump_924 -> Integer
d_next'45'slot'45'delta_930 v0
  = case coe v0 of
      C_mkBump_934 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_932 :: T_AllocBump_924 -> Integer
d_next'45'heap'45'ref'45'delta_932 v0
  = case coe v0 of
      C_mkBump_934 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump
d_apply'45'bump_936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_936 ~v0 v1 v2 = du_apply'45'bump_936 v1 v2
du_apply'45'bump_936 ::
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_936 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v1))
      (coe
         addInt (coe d_next'45'slot'45'delta_930 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_932 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v1))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-0
d_bump'45'0_942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924
d_bump'45'0_942 ~v0 = du_bump'45'0_942
du_bump'45'0_942 :: T_AllocBump_924
du_bump'45'0_942
  = coe C_mkBump_934 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-+
d_bump'45''43'_944 ::
  T_AllocBump_924 -> T_AllocBump_924 -> T_AllocBump_924
d_bump'45''43'_944 v0 v1
  = coe
      C_mkBump_934
      (coe
         addInt (coe d_next'45'slot'45'delta_930 (coe v0))
         (coe d_next'45'slot'45'delta_930 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_932 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_932 (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_954 ::
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_954 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924 ->
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_962 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant._.compose-eq
d_compose'45'eq_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924 ->
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'eq_980 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_996 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_996 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump
d_AllocBump_1040 a0 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.BeforeFrontier
d_BeforeFrontier_1044 a0 a1 a2 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.StackAncestorSource
d_StackAncestorSource_1046 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump
d_apply'45'bump_1048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_1048 ~v0 = du_apply'45'bump_1048
du_apply'45'bump_1048 ::
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_1048 = coe du_apply'45'bump_936
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1050 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1050 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-compose
d_apply'45'bump'45'compose_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924 ->
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_1052 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_1054 ::
  T_AllocBump_924 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_1054 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_1056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_658 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_1056 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.bump-+
d_bump'45''43'_1058 ::
  T_AllocBump_924 -> T_AllocBump_924 -> T_AllocBump_924
d_bump'45''43'_1058 v0 v1
  = coe
      C_mkBump_934
      (coe
         addInt (coe d_next'45'slot'45'delta_930 (coe v0))
         (coe d_next'45'slot'45'delta_930 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_932 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_932 (coe v1)))
-- Once.CCC.Machine.Allocation.FrameOps._.bump-0
d_bump'45'0_1060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_924
d_bump'45'0_1060 ~v0 = du_bump'45'0_1060
du_bump'45'0_1060 :: T_AllocBump_924
du_bump'45'0_1060 = coe du_bump'45'0_942
-- Once.CCC.Machine.Allocation.FrameOps._.fresh-stack-after
d_fresh'45'stack'45'after_1062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1062 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.frontier-monotone
d_frontier'45'monotone_1064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_frontier'45'monotone_1064 ~v0 = du_frontier'45'monotone_1064
du_frontier'45'monotone_1064 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_frontier'45'monotone_1064 v0 v1 v2 v3 v4 v5 v6
  = coe du_frontier'45'monotone_862 v3 v4 v5 v6
-- Once.CCC.Machine.Allocation.FrameOps._.heap-alloc-advances
d_heap'45'alloc'45'advances_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_heap'45'alloc'45'advances_1066 ~v0
  = du_heap'45'alloc'45'advances_1066
du_heap'45'alloc'45'advances_1066 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_heap'45'alloc'45'advances_1066
  = coe du_heap'45'alloc'45'advances_828
-- Once.CCC.Machine.Allocation.FrameOps._.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1072 :: T_AllocBump_924 -> Integer
d_next'45'heap'45'ref'45'delta_1072 v0
  = coe d_next'45'heap'45'ref'45'delta_932 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.next-slot-delta
d_next'45'slot'45'delta_1074 :: T_AllocBump_924 -> Integer
d_next'45'slot'45'delta_1074 v0
  = coe d_next'45'slot'45'delta_930 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.stack-alloc-advances
d_stack'45'alloc'45'advances_1080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_stack'45'alloc'45'advances_1080 ~v0
  = du_stack'45'alloc'45'advances_1080
du_stack'45'alloc'45'advances_1080 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_stack'45'alloc'45'advances_1080 v0 v1 v2 v3
  = coe du_stack'45'alloc'45'advances_792 v0 v2 v3
-- Once.CCC.Machine.Allocation.FrameOps._.≺⇒≢
d_'8826''8658''8802'_1086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1086 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1090 :: T_AllocBump_924 -> Integer
d_next'45'heap'45'ref'45'delta_1090 v0
  = coe d_next'45'heap'45'ref'45'delta_932 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1092 :: T_AllocBump_924 -> Integer
d_next'45'slot'45'delta_1092 v0
  = coe d_next'45'slot'45'delta_930 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps.push-frame
d_push'45'frame_1114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_push'45'frame_1114 ~v0 v1 v2 v3 = du_push'45'frame_1114 v1 v2 v3
du_push'45'frame_1114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_push'45'frame_1114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
               (coe v0))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe v0)))
      (coe v2) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.pop-frame
d_pop'45'frame_1128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_pop'45'frame_1128 ~v0 v1 v2 v3 = du_pop'45'frame_1128 v1 v2 v3
du_pop'45'frame_1128 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_pop'45'frame_1128 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_588
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_586 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.in-parent-frame-before-child
d_in'45'parent'45'frame'45'before'45'child_1144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
d_in'45'parent'45'frame'45'before'45'child_1144 v0 ~v1 ~v2 ~v3 v4
                                                v5
  = du_in'45'parent'45'frame'45'before'45'child_1144 v0 v4 v5
du_in'45'parent'45'frame'45'before'45'child_1144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
du_in'45'parent'45'frame'45'before'45'child_1144 v0 v1 v2
  = coe
      C_stack'45'ancestor_676
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      v1 (coe C_src'45'origin_646 v2)
-- Once.CCC.Machine.Allocation.FrameOps.heap-before-child
d_heap'45'before'45'child_1166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
d_heap'45'before'45'child_1166 ~v0 ~v1 ~v2 ~v3 v4
  = du_heap'45'before'45'child_1166 v4
du_heap'45'before'45'child_1166 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
du_heap'45'before'45'child_1166 v0 = coe C_heap'45'before_680 v0
-- Once.CCC.Machine.Allocation.FrameOps.ancestor-frame-before-child
d_ancestor'45'frame'45'before'45'child_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_658
d_ancestor'45'frame'45'before'45'child_1192 v0 v1 v2 ~v3 v4 ~v5 v6
                                            v7 v8 v9
  = du_ancestor'45'frame'45'before'45'child_1192
      v0 v1 v2 v4 v6 v7 v8 v9
du_ancestor'45'frame'45'before'45'child_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_658
du_ancestor'45'frame'45'before'45'child_1192 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      C_stack'45'ancestor_676
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
         (coe v1))
      v4
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_134 v0 v2
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v1))
         v3 v6 v7)
      (coe C_src'45'above'45'origin_654 v7 v5)
-- Once.CCC.Machine.Allocation.FrameOps.parent-before-child
d_parent'45'before'45'child_1220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_658 -> T_BeforeFrontier_658
d_parent'45'before'45'child_1220 v0 v1 v2 ~v3 v4 v5 v6
  = du_parent'45'before'45'child_1220 v0 v1 v2 v4 v5 v6
du_parent'45'before'45'child_1220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_658 -> T_BeforeFrontier_658
du_parent'45'before'45'child_1220 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
        -> case coe v5 of
             C_stack'45'before_666 v11
               -> coe
                    C_stack'45'ancestor_676
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                       (coe v1))
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v1))
                    v4 (coe C_src'45'origin_646 v11)
             C_stack'45'ancestor_676 v10 v11 v12 v13
               -> case coe v13 of
                    C_src'45'origin_646 v16
                      -> coe
                           C_stack'45'ancestor_676
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_134 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_654 v12 v16)
                    C_src'45'above'45'origin_654 v16 v18
                      -> coe
                           C_stack'45'ancestor_676
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_134 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_654 v12 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
        -> case coe v5 of
             C_heap'45'before_680 v8 -> coe C_heap'45'before_680 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrameOps.pop-preserves-before
d_pop'45'preserves'45'before_1292 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
d_pop'45'preserves'45'before_1292 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'preserves'45'before_1292 v4
du_pop'45'preserves'45'before_1292 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
du_pop'45'preserves'45'before_1292 v0
  = coe C_stack'45'before_666 v0
-- Once.CCC.Machine.Allocation.FrameOps.pop-heap-before
d_pop'45'heap'45'before_1312 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
d_pop'45'heap'45'before_1312 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'heap'45'before_1312 v4
du_pop'45'heap'45'before_1312 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_658
du_pop'45'heap'45'before_1312 v0 = coe C_heap'45'before_680 v0
