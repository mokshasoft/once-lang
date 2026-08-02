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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_48 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-loc
d_stack'45'alloc'45'loc_58 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_58 v0 ~v1 = du_stack'45'alloc'45'loc_58 v0
du_stack'45'alloc'45'loc_58 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-state
d_stack'45'alloc'45'state_68 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_stack'45'alloc'45'state_68 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_80 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_80 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_80 v0
du_stack'45'alloc'45'in'45'frame_80 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_80 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-offset
d_stack'45'alloc'45'offset_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_92 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_92 v0 v2
du_stack'45'alloc'45'offset_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_92 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc
d_heap'45'alloc_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_110 v0 ~v1 = du_heap'45'alloc_110 v0
du_heap'45'alloc_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
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
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-hl
d_heap'45'alloc'45'hl_120 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_120 v0 ~v1 = du_heap'45'alloc'45'hl_120 v0
du_heap'45'alloc'45'hl_120 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_120 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-loc
d_heap'45'alloc'45'loc_130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_130 v0 ~v1 = du_heap'45'alloc'45'loc_130 v0
du_heap'45'alloc'45'loc_130 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_130 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-state
d_heap'45'alloc'45'state_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_heap'45'alloc'45'state_140 v0 ~v1
  = du_heap'45'alloc'45'state_140 v0
du_heap'45'alloc'45'state_140 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_heap'45'alloc'45'state_140 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc
d_stack'45'alloc_152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_152 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_154 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_154 v0
du_stack'45'alloc'45'in'45'frame_154 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_154 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-loc
d_stack'45'alloc'45'loc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'loc_156 v0 ~v1
  = du_stack'45'alloc'45'loc_156 v0
du_stack'45'alloc'45'loc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'loc_156 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-offset
d_stack'45'alloc'45'offset_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_stack'45'alloc'45'offset_158 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_158 v0 v2
du_stack'45'alloc'45'offset_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_stack'45'alloc'45'offset_158 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-state
d_stack'45'alloc'45'state_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_stack'45'alloc'45'state_160 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc
d_heap'45'alloc_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_164 v0 ~v1 = du_heap'45'alloc_164 v0
du_heap'45'alloc_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
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
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-hl
d_heap'45'alloc'45'hl_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_166 v0 ~v1 = du_heap'45'alloc'45'hl_166 v0
du_heap'45'alloc'45'hl_166 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_166 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-loc
d_heap'45'alloc'45'loc_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_heap'45'alloc'45'loc_168 v0 ~v1 = du_heap'45'alloc'45'loc_168 v0
du_heap'45'alloc'45'loc_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_heap'45'alloc'45'loc_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-state
d_heap'45'alloc'45'state_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_heap'45'alloc'45'state_170 v0 ~v1
  = du_heap'45'alloc'45'state_170 v0
du_heap'45'alloc'45'state_170 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_heap'45'alloc'45'state_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator.AllocResult
d_AllocResult_176 a0 a1 a2 = ()
data T_AllocResult_176
  = C_constructor_190 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                      MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
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
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_new'45'state_188 v0
  = case coe v0 of
      C_constructor_190 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.alloc-stack
d_alloc'45'stack_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> T_AllocResult_176
d_alloc'45'stack_196 ~v0 v1 v2 = du_alloc'45'stack_196 v1 v2
du_alloc'45'stack_196 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> T_AllocResult_176
du_alloc'45'stack_196 v0 v1
  = coe
      C_constructor_190
      (coe
         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.alloc-heap
d_alloc'45'heap_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> T_AllocResult_176
d_alloc'45'heap_206 ~v0 v1 ~v2 = du_alloc'45'heap_206 v1
du_alloc'45'heap_206 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
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
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
               (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0)))
-- Once.CCC.Machine.Allocation.LocStateWithAlloc
d_LocStateWithAlloc_214 a0 = ()
data T_LocStateWithAlloc_214
  = C_mkLocStateWithAlloc_226 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
                              MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.machine-state
d_machine'45'state_222 ::
  T_LocStateWithAlloc_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_machine'45'state_222 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_226 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.alloc-state
d_alloc'45'state_224 ::
  T_LocStateWithAlloc_214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_alloc'45'state_224 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_226 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-slot
d_write'45'stack'45'slot_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_write'45'stack'45'slot_300 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_560
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_794 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554 (coe v1))
         (coe v2) (coe v3) (coe v4))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v1))
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-slot
d_write'45'heap'45'slot_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_write'45'heap'45'slot_310 ~v0 v1 v2 v3
  = du_write'45'heap'45'slot_310 v1 v2 v3
du_write'45'heap'45'slot_310 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_write'45'heap'45'slot_310 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_560
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_818
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556 (coe v0))
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v0))
-- Once.CCC.Machine.Allocation.WriteOps.write-loc
d_write'45'loc_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_write'45'loc_318 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_write'45'stack'45'slot_300 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe v1
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_write'45'heap'45'slot_310 (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-preserves-diff
d_write'45'stack'45'preserves'45'diff_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'preserves'45'diff_350 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-read-same
d_write'45'stack'45'read'45'same_466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'read'45'same_466 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-read-same
d_write'45'heap'45'read'45'same_514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'heap'45'read'45'same_514 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_614 a0 a1 a2 a3 a4 = ()
data T_StackAncestorSource_614
  = C_src'45'origin_622 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_src'45'above'45'origin_630 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_634 a0 a1 a2 = ()
data T_BeforeFrontier_634
  = C_stack'45'before_642 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_stack'45'ancestor_652 AgdaAny Integer AgdaAny
                            T_StackAncestorSource_614 |
    C_heap'45'before_656 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_662 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_674 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_634 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_734 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_stack'45'alloc'45'advances_768 ~v0 v1 ~v2 v3 v4
  = du_stack'45'alloc'45'advances_768 v1 v3 v4
du_stack'45'alloc'45'advances_768 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_stack'45'alloc'45'advances_768 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_642 v8
               -> coe
                    C_stack'45'before_642
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v8)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))))
             C_stack'45'ancestor_652 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_652 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_656 v5 -> coe C_heap'45'before_656 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_heap'45'alloc'45'advances_804 ~v0 v1 v2 v3
  = du_heap'45'alloc'45'advances_804 v1 v2 v3
du_heap'45'alloc'45'advances_804 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_heap'45'alloc'45'advances_804 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
        -> case coe v2 of
             C_stack'45'before_642 v8 -> coe C_stack'45'before_642 v8
             C_stack'45'ancestor_652 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_652 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
        -> case coe v2 of
             C_heap'45'before_656 v5
               -> coe
                    C_heap'45'before_656
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v5)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                             (coe v0))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.frontier-monotone
d_frontier'45'monotone_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_frontier'45'monotone_838 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_frontier'45'monotone_838 v4 v5 v6 v7
du_frontier'45'monotone_838 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_frontier'45'monotone_838 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> case coe v3 of
             C_stack'45'before_642 v9
               -> coe
                    C_stack'45'before_642
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v9) (coe v0))
             C_stack'45'ancestor_652 v8 v9 v10 v11
               -> coe C_stack'45'ancestor_652 v8 v9 v10 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_heap'45'before_656 v6
               -> coe
                    C_heap'45'before_656
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v6) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump
d_AllocBump_900 a0 = ()
data T_AllocBump_900 = C_mkBump_910 Integer Integer
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_906 :: T_AllocBump_900 -> Integer
d_next'45'slot'45'delta_906 v0
  = case coe v0 of
      C_mkBump_910 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_908 :: T_AllocBump_900 -> Integer
d_next'45'heap'45'ref'45'delta_908 v0
  = case coe v0 of
      C_mkBump_910 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump
d_apply'45'bump_912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_apply'45'bump_912 ~v0 v1 v2 = du_apply'45'bump_912 v1 v2
du_apply'45'bump_912 ::
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_apply'45'bump_912 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v1))
      (coe
         addInt (coe d_next'45'slot'45'delta_906 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_908 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
            (coe v1)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v1))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-0
d_bump'45'0_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900
d_bump'45'0_918 ~v0 = du_bump'45'0_918
du_bump'45'0_918 :: T_AllocBump_900
du_bump'45'0_918
  = coe C_mkBump_910 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-+
d_bump'45''43'_920 ::
  T_AllocBump_900 -> T_AllocBump_900 -> T_AllocBump_900
d_bump'45''43'_920 v0 v1
  = coe
      C_mkBump_910
      (coe
         addInt (coe d_next'45'slot'45'delta_906 (coe v0))
         (coe d_next'45'slot'45'delta_906 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_908 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_908 (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_930 ::
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_930 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900 ->
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_938 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant._.compose-eq
d_compose'45'eq_956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900 ->
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'eq_956 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_972 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_972 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump
d_AllocBump_1012 a0 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.BeforeFrontier
d_BeforeFrontier_1016 a0 a1 a2 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.StackAncestorSource
d_StackAncestorSource_1018 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump
d_apply'45'bump_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_apply'45'bump_1020 ~v0 = du_apply'45'bump_1020
du_apply'45'bump_1020 ::
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_apply'45'bump_1020 = coe du_apply'45'bump_912
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_1022 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_1022 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-compose
d_apply'45'bump'45'compose_1024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900 ->
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_1024 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_1026 ::
  T_AllocBump_900 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_1026 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_1028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  T_BeforeFrontier_634 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_1028 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.bump-+
d_bump'45''43'_1030 ::
  T_AllocBump_900 -> T_AllocBump_900 -> T_AllocBump_900
d_bump'45''43'_1030 v0 v1
  = coe
      C_mkBump_910
      (coe
         addInt (coe d_next'45'slot'45'delta_906 (coe v0))
         (coe d_next'45'slot'45'delta_906 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_908 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_908 (coe v1)))
-- Once.CCC.Machine.Allocation.FrameOps._.bump-0
d_bump'45'0_1032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_900
d_bump'45'0_1032 ~v0 = du_bump'45'0_1032
du_bump'45'0_1032 :: T_AllocBump_900
du_bump'45'0_1032 = coe du_bump'45'0_918
-- Once.CCC.Machine.Allocation.FrameOps._.fresh-stack-after
d_fresh'45'stack'45'after_1034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1034 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.frontier-monotone
d_frontier'45'monotone_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_frontier'45'monotone_1036 ~v0 = du_frontier'45'monotone_1036
du_frontier'45'monotone_1036 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_frontier'45'monotone_1036 v0 v1 v2 v3 v4 v5 v6
  = coe du_frontier'45'monotone_838 v3 v4 v5 v6
-- Once.CCC.Machine.Allocation.FrameOps._.heap-alloc-advances
d_heap'45'alloc'45'advances_1038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_heap'45'alloc'45'advances_1038 ~v0
  = du_heap'45'alloc'45'advances_1038
du_heap'45'alloc'45'advances_1038 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_heap'45'alloc'45'advances_1038
  = coe du_heap'45'alloc'45'advances_804
-- Once.CCC.Machine.Allocation.FrameOps._.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1044 :: T_AllocBump_900 -> Integer
d_next'45'heap'45'ref'45'delta_1044 v0
  = coe d_next'45'heap'45'ref'45'delta_908 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.next-slot-delta
d_next'45'slot'45'delta_1046 :: T_AllocBump_900 -> Integer
d_next'45'slot'45'delta_1046 v0
  = coe d_next'45'slot'45'delta_906 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.stack-alloc-advances
d_stack'45'alloc'45'advances_1052 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_stack'45'alloc'45'advances_1052 ~v0
  = du_stack'45'alloc'45'advances_1052
du_stack'45'alloc'45'advances_1052 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_stack'45'alloc'45'advances_1052 v0 v1 v2 v3
  = coe du_stack'45'alloc'45'advances_768 v0 v2 v3
-- Once.CCC.Machine.Allocation.FrameOps._.≺⇒≢
d_'8826''8658''8802'_1058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1058 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1062 :: T_AllocBump_900 -> Integer
d_next'45'heap'45'ref'45'delta_1062 v0
  = coe d_next'45'heap'45'ref'45'delta_908 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1064 :: T_AllocBump_900 -> Integer
d_next'45'slot'45'delta_1064 v0
  = coe d_next'45'slot'45'delta_906 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps.push-frame
d_push'45'frame_1086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_push'45'frame_1086 ~v0 v1 v2 ~v3 = du_push'45'frame_1086 v1 v2
du_push'45'frame_1086 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_push'45'frame_1086 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v0)))
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.pop-frame
d_pop'45'frame_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_pop'45'frame_1098 ~v0 v1 v2 v3 = du_pop'45'frame_1098 v1 v2 v3
du_pop'45'frame_1098 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_pop'45'frame_1098 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.in-parent-frame-before-child
d_in'45'parent'45'frame'45'before'45'child_1114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
d_in'45'parent'45'frame'45'before'45'child_1114 v0 ~v1 ~v2 ~v3 v4
                                                v5
  = du_in'45'parent'45'frame'45'before'45'child_1114 v0 v4 v5
du_in'45'parent'45'frame'45'before'45'child_1114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
du_in'45'parent'45'frame'45'before'45'child_1114 v0 v1 v2
  = coe
      C_stack'45'ancestor_652
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v0))
      v1 (coe C_src'45'origin_622 v2)
-- Once.CCC.Machine.Allocation.FrameOps.heap-before-child
d_heap'45'before'45'child_1136 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
d_heap'45'before'45'child_1136 ~v0 ~v1 ~v2 ~v3 v4
  = du_heap'45'before'45'child_1136 v4
du_heap'45'before'45'child_1136 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
du_heap'45'before'45'child_1136 v0 = coe C_heap'45'before_656 v0
-- Once.CCC.Machine.Allocation.FrameOps.ancestor-frame-before-child
d_ancestor'45'frame'45'before'45'child_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_634
d_ancestor'45'frame'45'before'45'child_1162 v0 v1 v2 ~v3 v4 ~v5 v6
                                            v7 v8 v9
  = du_ancestor'45'frame'45'before'45'child_1162
      v0 v1 v2 v4 v6 v7 v8 v9
du_ancestor'45'frame'45'before'45'child_1162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_634
du_ancestor'45'frame'45'before'45'child_1162 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      C_stack'45'ancestor_652
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
         (coe v1))
      v4
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_126 v0 v2
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v1))
         v3 v6 v7)
      (coe C_src'45'above'45'origin_630 v7 v5)
-- Once.CCC.Machine.Allocation.FrameOps.parent-before-child
d_parent'45'before'45'child_1190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_634 -> T_BeforeFrontier_634
d_parent'45'before'45'child_1190 v0 v1 v2 ~v3 v4 v5 v6
  = du_parent'45'before'45'child_1190 v0 v1 v2 v4 v5 v6
du_parent'45'before'45'child_1190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> T_BeforeFrontier_634 -> T_BeforeFrontier_634
du_parent'45'before'45'child_1190 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
        -> case coe v5 of
             C_stack'45'before_642 v11
               -> coe
                    C_stack'45'ancestor_652
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                       (coe v1))
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v1))
                    v4 (coe C_src'45'origin_622 v11)
             C_stack'45'ancestor_652 v10 v11 v12 v13
               -> case coe v13 of
                    C_src'45'origin_622 v16
                      -> coe
                           C_stack'45'ancestor_652
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_126 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_630 v12 v16)
                    C_src'45'above'45'origin_630 v16 v18
                      -> coe
                           C_stack'45'ancestor_652
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_126 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_630 v12 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
        -> case coe v5 of
             C_heap'45'before_656 v8 -> coe C_heap'45'before_656 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrameOps.pop-preserves-before
d_pop'45'preserves'45'before_1262 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
d_pop'45'preserves'45'before_1262 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'preserves'45'before_1262 v4
du_pop'45'preserves'45'before_1262 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
du_pop'45'preserves'45'before_1262 v0
  = coe C_stack'45'before_642 v0
-- Once.CCC.Machine.Allocation.FrameOps.pop-heap-before
d_pop'45'heap'45'before_1282 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
d_pop'45'heap'45'before_1282 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'heap'45'before_1282 v4
du_pop'45'heap'45'before_1282 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_634
du_pop'45'heap'45'before_1282 v0 = coe C_heap'45'before_656 v0
