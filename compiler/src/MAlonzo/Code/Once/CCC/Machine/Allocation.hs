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
d_stack'45'alloc_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_50 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0)))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-loc
d_stack'45'alloc'45'loc_60 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_60 v0 ~v1 = du_stack'45'alloc'45'loc_60 v0
du_stack'45'alloc'45'loc_60 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_60 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-state
d_stack'45'alloc'45'state_70 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_stack'45'alloc'45'state_70 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_82 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_82 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_82 v0
du_stack'45'alloc'45'in'45'frame_82 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_82 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-offset
d_stack'45'alloc'45'offset_94 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_94 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_94 v0 v2
du_stack'45'alloc'45'offset_94 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_94 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc
d_heap'45'alloc_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_112 v0 ~v1 = du_heap'45'alloc_112 v0
du_heap'45'alloc_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_112 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-hl
d_heap'45'alloc'45'hl_122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_122 v0 ~v1 = du_heap'45'alloc'45'hl_122 v0
du_heap'45'alloc'45'hl_122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_122 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-loc
d_heap'45'alloc'45'loc_132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_132 v0 ~v1 = du_heap'45'alloc'45'loc_132 v0
du_heap'45'alloc'45'loc_132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_132 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-state
d_heap'45'alloc'45'state_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_heap'45'alloc'45'state_142 v0 ~v1
  = du_heap'45'alloc'45'state_142 v0
du_heap'45'alloc'45'state_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_heap'45'alloc'45'state_142 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc
d_stack'45'alloc_154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_154 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_156 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_156 v0
du_stack'45'alloc'45'in'45'frame_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_156 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-loc
d_stack'45'alloc'45'loc_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_158 v0 ~v1
  = du_stack'45'alloc'45'loc_158 v0
du_stack'45'alloc'45'loc_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_158 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-offset
d_stack'45'alloc'45'offset_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_160 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_160 v0 v2
du_stack'45'alloc'45'offset_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_160 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-state
d_stack'45'alloc'45'state_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_stack'45'alloc'45'state_162 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc
d_heap'45'alloc_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_166 v0 ~v1 = du_heap'45'alloc_166 v0
du_heap'45'alloc_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_166 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-hl
d_heap'45'alloc'45'hl_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_168 v0 ~v1 = du_heap'45'alloc'45'hl_168 v0
du_heap'45'alloc'45'hl_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_168 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-loc
d_heap'45'alloc'45'loc_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_170 v0 ~v1 = du_heap'45'alloc'45'loc_170 v0
du_heap'45'alloc'45'loc_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-state
d_heap'45'alloc'45'state_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_heap'45'alloc'45'state_172 v0 ~v1
  = du_heap'45'alloc'45'state_172 v0
du_heap'45'alloc'45'state_172 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_heap'45'alloc'45'state_172 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator.AllocResult
d_AllocResult_178 a0 a1 a2 = ()
data T_AllocResult_178
  = C_constructor_192 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.location
d_location_188 ::
  T_AllocResult_178 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_location_188 v0
  = case coe v0 of
      C_constructor_192 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.new-state
d_new'45'state_190 ::
  T_AllocResult_178 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_new'45'state_190 v0
  = case coe v0 of
      C_constructor_192 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.alloc-stack
d_alloc'45'stack_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_AllocResult_178
d_alloc'45'stack_198 ~v0 v1 v2 = du_alloc'45'stack_198 v1 v2
du_alloc'45'stack_198 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_AllocResult_178
du_alloc'45'stack_198 v0 v1
  = coe
      C_constructor_192
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.alloc-heap
d_alloc'45'heap_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_AllocResult_178
d_alloc'45'heap_208 ~v0 v1 ~v2 = du_alloc'45'heap_208 v1
du_alloc'45'heap_208 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  T_AllocResult_178
du_alloc'45'heap_208 v0
  = coe
      C_constructor_192
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0)))
-- Once.CCC.Machine.Allocation.LocStateWithAlloc
d_LocStateWithAlloc_216 a0 = ()
data T_LocStateWithAlloc_216
  = C_mkLocStateWithAlloc_228 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
                              MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.machine-state
d_machine'45'state_224 ::
  T_LocStateWithAlloc_216 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_machine'45'state_224 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_228 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.alloc-state
d_alloc'45'state_226 ::
  T_LocStateWithAlloc_216 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_alloc'45'state_226 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_228 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-slot
d_write'45'stack'45'slot_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'stack'45'slot_310 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_666 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 (coe v1))
         (coe v2) (coe v3) (coe v4))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v1))
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-slot
d_write'45'heap'45'slot_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'heap'45'slot_320 ~v0 v1 v2 v3
  = du_write'45'heap'45'slot_320 v1 v2 v3
du_write'45'heap'45'slot_320 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_write'45'heap'45'slot_320 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_776
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 (coe v0))
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v0))
-- Once.CCC.Machine.Allocation.WriteOps.write-loc
d_write'45'loc_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_write'45'loc_328 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_write'45'stack'45'slot_310 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_write'45'heap'45'slot_320 (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-preserves-diff
d_write'45'stack'45'preserves'45'diff_360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'preserves'45'diff_360 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-read-same
d_write'45'stack'45'read'45'same_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'read'45'same_476 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-read-same
d_write'45'heap'45'read'45'same_524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'heap'45'read'45'same_524 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_632 a0 a1 a2 a3 a4 = ()
data T_StackAncestorSource_632
  = C_src'45'origin_640 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_src'45'above'45'origin_648 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_652 a0 a1 a2 = ()
data T_BeforeFrontier_652
  = C_stack'45'before_660 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_stack'45'ancestor_670 AgdaAny Integer AgdaAny
                            T_StackAncestorSource_632 |
    C_heap'45'before_674 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_680 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_692 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_652 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_752 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_stack'45'alloc'45'advances_786 ~v0 v1 ~v2 v3 v4
  = du_stack'45'alloc'45'advances_786 v1 v3 v4
du_stack'45'alloc'45'advances_786 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_stack'45'alloc'45'advances_786 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_660 v8
               -> coe
                    C_stack'45'before_660
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v8)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))))
             C_stack'45'ancestor_670 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_670 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_674 v5 -> coe C_heap'45'before_674 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_heap'45'alloc'45'advances_822 ~v0 v1 v2 v3
  = du_heap'45'alloc'45'advances_822 v1 v2 v3
du_heap'45'alloc'45'advances_822 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_heap'45'alloc'45'advances_822 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_660 v8 -> coe C_stack'45'before_660 v8
             C_stack'45'ancestor_670 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_670 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_674 v5
               -> coe
                    C_heap'45'before_674
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v5)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
                             (coe v0))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_frontier'45'monotone_856 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_frontier'45'monotone_856 v4 v5 v6 v7
du_frontier'45'monotone_856 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_frontier'45'monotone_856 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> case coe v3 of
             C_stack'45'before_660 v9
               -> coe
                    C_stack'45'before_660
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v9) (coe v0))
             C_stack'45'ancestor_670 v8 v9 v10 v11
               -> coe C_stack'45'ancestor_670 v8 v9 v10 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_heap'45'before_674 v6
               -> coe
                    C_heap'45'before_674
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v6) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump
d_AllocBump_918 a0 = ()
data T_AllocBump_918 = C_mkBump_928 Integer Integer
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_924 :: T_AllocBump_918 -> Integer
d_next'45'slot'45'delta_924 v0
  = case coe v0 of
      C_mkBump_928 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_926 :: T_AllocBump_918 -> Integer
d_next'45'heap'45'ref'45'delta_926 v0
  = case coe v0 of
      C_mkBump_928 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump
d_apply'45'bump_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_930 ~v0 v1 v2 = du_apply'45'bump_930 v1 v2
du_apply'45'bump_930 ::
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_930 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v1))
      (coe
         addInt (coe d_next'45'slot'45'delta_924 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_926 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v1))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-0
d_bump'45'0_936 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918
d_bump'45'0_936 ~v0 = du_bump'45'0_936
du_bump'45'0_936 :: T_AllocBump_918
du_bump'45'0_936
  = coe C_mkBump_928 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-+
d_bump'45''43'_938 ::
  T_AllocBump_918 -> T_AllocBump_918 -> T_AllocBump_918
d_bump'45''43'_938 v0 v1
  = coe
      C_mkBump_928
      (coe
         addInt (coe d_next'45'slot'45'delta_924 (coe v0))
         (coe d_next'45'slot'45'delta_924 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_926 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_926 (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_948 ::
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_948 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918 ->
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_956 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant._.compose-eq
d_compose'45'eq_974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918 ->
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'eq_974 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_990 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_990 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump
d_AllocBump_1032 a0 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.BeforeFrontier
d_BeforeFrontier_1036 a0 a1 a2 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.StackAncestorSource
d_StackAncestorSource_1038 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump
d_apply'45'bump_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_apply'45'bump_1040 ~v0 = du_apply'45'bump_1040
du_apply'45'bump_1040 ::
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_apply'45'bump_1040 = coe du_apply'45'bump_930
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1042 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1042 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-compose
d_apply'45'bump'45'compose_1044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918 ->
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_1044 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_1046 ::
  T_AllocBump_918 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_1046 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_1048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_652 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_1048 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.bump-+
d_bump'45''43'_1050 ::
  T_AllocBump_918 -> T_AllocBump_918 -> T_AllocBump_918
d_bump'45''43'_1050 v0 v1
  = coe
      C_mkBump_928
      (coe
         addInt (coe d_next'45'slot'45'delta_924 (coe v0))
         (coe d_next'45'slot'45'delta_924 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_926 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_926 (coe v1)))
-- Once.CCC.Machine.Allocation.FrameOps._.bump-0
d_bump'45'0_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_918
d_bump'45'0_1052 ~v0 = du_bump'45'0_1052
du_bump'45'0_1052 :: T_AllocBump_918
du_bump'45'0_1052 = coe du_bump'45'0_936
-- Once.CCC.Machine.Allocation.FrameOps._.fresh-stack-after
d_fresh'45'stack'45'after_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1054 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.frontier-monotone
d_frontier'45'monotone_1056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_frontier'45'monotone_1056 ~v0 = du_frontier'45'monotone_1056
du_frontier'45'monotone_1056 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_frontier'45'monotone_1056 v0 v1 v2 v3 v4 v5 v6
  = coe du_frontier'45'monotone_856 v3 v4 v5 v6
-- Once.CCC.Machine.Allocation.FrameOps._.heap-alloc-advances
d_heap'45'alloc'45'advances_1058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_heap'45'alloc'45'advances_1058 ~v0
  = du_heap'45'alloc'45'advances_1058
du_heap'45'alloc'45'advances_1058 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_heap'45'alloc'45'advances_1058
  = coe du_heap'45'alloc'45'advances_822
-- Once.CCC.Machine.Allocation.FrameOps._.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1064 :: T_AllocBump_918 -> Integer
d_next'45'heap'45'ref'45'delta_1064 v0
  = coe d_next'45'heap'45'ref'45'delta_926 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.next-slot-delta
d_next'45'slot'45'delta_1066 :: T_AllocBump_918 -> Integer
d_next'45'slot'45'delta_1066 v0
  = coe d_next'45'slot'45'delta_924 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.stack-alloc-advances
d_stack'45'alloc'45'advances_1072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_stack'45'alloc'45'advances_1072 ~v0
  = du_stack'45'alloc'45'advances_1072
du_stack'45'alloc'45'advances_1072 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_stack'45'alloc'45'advances_1072 v0 v1 v2 v3
  = coe du_stack'45'alloc'45'advances_786 v0 v2 v3
-- Once.CCC.Machine.Allocation.FrameOps._.≺⇒≢
d_'8826''8658''8802'_1078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1078 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1082 :: T_AllocBump_918 -> Integer
d_next'45'heap'45'ref'45'delta_1082 v0
  = coe d_next'45'heap'45'ref'45'delta_926 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1084 :: T_AllocBump_918 -> Integer
d_next'45'slot'45'delta_1084 v0
  = coe d_next'45'slot'45'delta_924 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps.push-frame
d_push'45'frame_1106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_push'45'frame_1106 ~v0 v1 v2 v3 = du_push'45'frame_1106 v1 v2 v3
du_push'45'frame_1106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_push'45'frame_1106 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
               (coe v0))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v0)))
      (coe v2) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.pop-frame
d_pop'45'frame_1120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_pop'45'frame_1120 ~v0 v1 v2 v3 = du_pop'45'frame_1120 v1 v2 v3
du_pop'45'frame_1120 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_pop'45'frame_1120 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.in-parent-frame-before-child
d_in'45'parent'45'frame'45'before'45'child_1136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
d_in'45'parent'45'frame'45'before'45'child_1136 v0 ~v1 ~v2 ~v3 v4
                                                v5
  = du_in'45'parent'45'frame'45'before'45'child_1136 v0 v4 v5
du_in'45'parent'45'frame'45'before'45'child_1136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
du_in'45'parent'45'frame'45'before'45'child_1136 v0 v1 v2
  = coe
      C_stack'45'ancestor_670
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v0))
      v1 (coe C_src'45'origin_640 v2)
-- Once.CCC.Machine.Allocation.FrameOps.heap-before-child
d_heap'45'before'45'child_1158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
d_heap'45'before'45'child_1158 ~v0 ~v1 ~v2 ~v3 v4
  = du_heap'45'before'45'child_1158 v4
du_heap'45'before'45'child_1158 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
du_heap'45'before'45'child_1158 v0 = coe C_heap'45'before_674 v0
-- Once.CCC.Machine.Allocation.FrameOps.ancestor-frame-before-child
d_ancestor'45'frame'45'before'45'child_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_652
d_ancestor'45'frame'45'before'45'child_1184 v0 v1 v2 ~v3 v4 ~v5 v6
                                            v7 v8 v9
  = du_ancestor'45'frame'45'before'45'child_1184
      v0 v1 v2 v4 v6 v7 v8 v9
du_ancestor'45'frame'45'before'45'child_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_652
du_ancestor'45'frame'45'before'45'child_1184 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      C_stack'45'ancestor_670
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
         (coe v1))
      v4
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_130 v0 v2
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v1))
         v3 v6 v7)
      (coe C_src'45'above'45'origin_648 v7 v5)
-- Once.CCC.Machine.Allocation.FrameOps.parent-before-child
d_parent'45'before'45'child_1212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_652 -> T_BeforeFrontier_652
d_parent'45'before'45'child_1212 v0 v1 v2 ~v3 v4 v5 v6
  = du_parent'45'before'45'child_1212 v0 v1 v2 v4 v5 v6
du_parent'45'before'45'child_1212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_652 -> T_BeforeFrontier_652
du_parent'45'before'45'child_1212 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
        -> case coe v5 of
             C_stack'45'before_660 v11
               -> coe
                    C_stack'45'ancestor_670
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
                       (coe v1))
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v1))
                    v4 (coe C_src'45'origin_640 v11)
             C_stack'45'ancestor_670 v10 v11 v12 v13
               -> case coe v13 of
                    C_src'45'origin_640 v16
                      -> coe
                           C_stack'45'ancestor_670
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_130 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_648 v12 v16)
                    C_src'45'above'45'origin_648 v16 v18
                      -> coe
                           C_stack'45'ancestor_670
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_130 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_648 v12 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
        -> case coe v5 of
             C_heap'45'before_674 v8 -> coe C_heap'45'before_674 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrameOps.pop-preserves-before
d_pop'45'preserves'45'before_1284 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
d_pop'45'preserves'45'before_1284 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'preserves'45'before_1284 v4
du_pop'45'preserves'45'before_1284 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
du_pop'45'preserves'45'before_1284 v0
  = coe C_stack'45'before_660 v0
-- Once.CCC.Machine.Allocation.FrameOps.pop-heap-before
d_pop'45'heap'45'before_1304 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
d_pop'45'heap'45'before_1304 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'heap'45'before_1304 v4
du_pop'45'heap'45'before_1304 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_652
du_pop'45'heap'45'before_1304 v0 = coe C_heap'45'before_674 v0
