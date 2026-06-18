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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress

-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc
d_stack'45'alloc_40 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_40 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-loc
d_stack'45'alloc'45'loc_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_stack'45'alloc'45'loc_50 v0 ~v1 = du_stack'45'alloc'45'loc_50 v0
du_stack'45'alloc'45'loc_50 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
du_stack'45'alloc'45'loc_50 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-state
d_stack'45'alloc'45'state_60 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_stack'45'alloc'45'state_60 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_72 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_72 v0
du_stack'45'alloc'45'in'45'frame_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_72 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.StackAllocation.stack-alloc-offset
d_stack'45'alloc'45'offset_84 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_stack'45'alloc'45'offset_84 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_84 v0 v2
du_stack'45'alloc'45'offset_84 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
du_stack'45'alloc'45'offset_84 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc
d_heap'45'alloc_102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_102 v0 ~v1 = du_heap'45'alloc_102 v0
du_heap'45'alloc_102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_102 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0))))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-hl
d_heap'45'alloc'45'hl_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_112 v0 ~v1 = du_heap'45'alloc'45'hl_112 v0
du_heap'45'alloc'45'hl_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_112 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-loc
d_heap'45'alloc'45'loc_122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_heap'45'alloc'45'loc_122 v0 ~v1 = du_heap'45'alloc'45'loc_122 v0
du_heap'45'alloc'45'loc_122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
du_heap'45'alloc'45'loc_122 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.HeapAllocation.heap-alloc-state
d_heap'45'alloc'45'state_132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_heap'45'alloc'45'state_132 v0 ~v1
  = du_heap'45'alloc'45'state_132 v0
du_heap'45'alloc'45'state_132 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
du_heap'45'alloc'45'state_132 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc
d_stack'45'alloc_144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc_144 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-in-frame
d_stack'45'alloc'45'in'45'frame_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'alloc'45'in'45'frame_146 v0 ~v1
  = du_stack'45'alloc'45'in'45'frame_146 v0
du_stack'45'alloc'45'in'45'frame_146 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stack'45'alloc'45'in'45'frame_146 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      erased
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-loc
d_stack'45'alloc'45'loc_148 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_stack'45'alloc'45'loc_148 v0 ~v1
  = du_stack'45'alloc'45'loc_148 v0
du_stack'45'alloc'45'loc_148 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
du_stack'45'alloc'45'loc_148 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-offset
d_stack'45'alloc'45'offset_150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_stack'45'alloc'45'offset_150 v0 ~v1 v2 ~v3
  = du_stack'45'alloc'45'offset_150 v0 v2
du_stack'45'alloc'45'offset_150 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
du_stack'45'alloc'45'offset_150 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
-- Once.CCC.Machine.Allocation.Allocator._.stack-alloc-state
d_stack'45'alloc'45'state_152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_stack'45'alloc'45'state_152 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc
d_heap'45'alloc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_heap'45'alloc_156 v0 ~v1 = du_heap'45'alloc_156 v0
du_heap'45'alloc_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_heap'45'alloc_156 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0))))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-hl
d_heap'45'alloc'45'hl_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
d_heap'45'alloc'45'hl_158 v0 ~v1 = du_heap'45'alloc'45'hl_158 v0
du_heap'45'alloc'45'hl_158 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
du_heap'45'alloc'45'hl_158 v0
  = coe
      MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
      (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-loc
d_heap'45'alloc'45'loc_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_heap'45'alloc'45'loc_160 v0 ~v1 = du_heap'45'alloc'45'loc_160 v0
du_heap'45'alloc'45'loc_160 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
du_heap'45'alloc'45'loc_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0)))
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Allocation.Allocator._.heap-alloc-state
d_heap'45'alloc'45'state_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_heap'45'alloc'45'state_162 v0 ~v1
  = du_heap'45'alloc'45'state_162 v0
du_heap'45'alloc'45'state_162 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
du_heap'45'alloc'45'state_162 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.AllocResult
d_AllocResult_168 a0 a1 a2 = ()
data T_AllocResult_168
  = C_constructor_182 MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
                      MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.location
d_location_178 ::
  T_AllocResult_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68
d_location_178 v0
  = case coe v0 of
      C_constructor_182 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.AllocResult.new-state
d_new'45'state_180 ::
  T_AllocResult_168 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_new'45'state_180 v0
  = case coe v0 of
      C_constructor_182 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.Allocator.alloc-stack
d_alloc'45'stack_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> T_AllocResult_168
d_alloc'45'stack_188 ~v0 v1 v2 = du_alloc'45'stack_188 v1 v2
du_alloc'45'stack_188 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> T_AllocResult_168
du_alloc'45'stack_188 v0 v1
  = coe
      C_constructor_182
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v0)))
-- Once.CCC.Machine.Allocation.Allocator.alloc-heap
d_alloc'45'heap_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> T_AllocResult_168
d_alloc'45'heap_198 ~v0 v1 ~v2 = du_alloc'45'heap_198 v1
du_alloc'45'heap_198 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  T_AllocResult_168
du_alloc'45'heap_198 v0
  = coe
      C_constructor_182
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.C_heap'45'loc_52
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.C_mkHeapRef_14
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
                  (coe v0)))
            (coe (0 :: Integer))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
         (coe
            addInt (coe (1 :: Integer))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
               (coe v0))))
-- Once.CCC.Machine.Allocation.LocStateWithAlloc
d_LocStateWithAlloc_206 a0 = ()
data T_LocStateWithAlloc_206
  = C_mkLocStateWithAlloc_218 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
                              MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.machine-state
d_machine'45'state_214 ::
  T_LocStateWithAlloc_206 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_machine'45'state_214 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_218 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.LocStateWithAlloc.alloc-state
d_alloc'45'state_216 ::
  T_LocStateWithAlloc_206 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_alloc'45'state_216 v0
  = case coe v0 of
      C_mkLocStateWithAlloc_218 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-slot
d_write'45'stack'45'slot_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_write'45'stack'45'slot_284 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_488
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_480 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeStackMem_658 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_482 (coe v1))
         (coe v2) (coe v3) (coe v4))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_484 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_486 (coe v1))
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-slot
d_write'45'heap'45'slot_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_write'45'heap'45'slot_294 ~v0 v1 v2 v3
  = du_write'45'heap'45'slot_294 v1 v2 v3
du_write'45'heap'45'slot_294 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
du_write'45'heap'45'slot_294 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_488
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_480 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_482 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_682
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_484 (coe v0))
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_486 (coe v0))
-- Once.CCC.Machine.Allocation.WriteOps.write-loc
d_write'45'loc_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_write'45'loc_302 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72 v4 v5
        -> coe
             d_write'45'stack'45'slot_284 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_82 (coe v3))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74 v4
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72 v5 v6 -> coe v1
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74 v5
               -> coe
                    du_write'45'heap'45'slot_294 (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_82 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-preserves-diff
d_write'45'stack'45'preserves'45'diff_334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'preserves'45'diff_334 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-stack-read-same
d_write'45'stack'45'read'45'same_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'stack'45'read'45'same_450 = erased
-- Once.CCC.Machine.Allocation.WriteOps.write-heap-read-same
d_write'45'heap'45'read'45'same_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'heap'45'read'45'same_498 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.StackAncestorSource
d_StackAncestorSource_590 a0 a1 a2 a3 a4 = ()
data T_StackAncestorSource_590
  = C_src'45'origin_598 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_src'45'above'45'origin_606 AgdaAny
                                 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.BeforeFrontier
d_BeforeFrontier_610 a0 a1 a2 = ()
data T_BeforeFrontier_610
  = C_stack'45'before_618 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_stack'45'ancestor_628 AgdaAny Integer AgdaAny
                            T_StackAncestorSource_590 |
    C_heap'45'before_632 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.Allocation.FrontierInvariant.≺⇒≢
d_'8826''8658''8802'_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_638 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.fresh-stack-after
d_fresh'45'stack'45'after_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_650 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  Integer ->
  T_BeforeFrontier_610 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_710 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.stack-alloc-advances
d_stack'45'alloc'45'advances_744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_stack'45'alloc'45'advances_744 ~v0 v1 ~v2 v3 v4
  = du_stack'45'alloc'45'advances_744 v1 v3 v4
du_stack'45'alloc'45'advances_744 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_stack'45'alloc'45'advances_744 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72 v3 v4
        -> case coe v2 of
             C_stack'45'before_618 v8
               -> coe
                    C_stack'45'before_618
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v8)
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))))
             C_stack'45'ancestor_628 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_628 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74 v3
        -> case coe v2 of
             C_heap'45'before_632 v5 -> coe C_heap'45'before_632 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.heap-alloc-advances
d_heap'45'alloc'45'advances_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_heap'45'alloc'45'advances_780 ~v0 v1 v2 v3
  = du_heap'45'alloc'45'advances_780 v1 v2 v3
du_heap'45'alloc'45'advances_780 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_heap'45'alloc'45'advances_780 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72 v3 v4
        -> case coe v2 of
             C_stack'45'before_618 v8 -> coe C_stack'45'before_618 v8
             C_stack'45'ancestor_628 v7 v8 v9 v10
               -> coe C_stack'45'ancestor_628 v7 v8 v9 v10
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74 v3
        -> case coe v2 of
             C_heap'45'before_632 v5
               -> coe
                    C_heap'45'before_632
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
d_frontier'45'monotone_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_frontier'45'monotone_814 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_frontier'45'monotone_814 v4 v5 v6 v7
du_frontier'45'monotone_814 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_frontier'45'monotone_814 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72 v4 v5
        -> case coe v3 of
             C_stack'45'before_618 v9
               -> coe
                    C_stack'45'before_618
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v9) (coe v0))
             C_stack'45'ancestor_628 v8 v9 v10 v11
               -> coe C_stack'45'ancestor_628 v8 v9 v10 v11
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74 v4
        -> case coe v3 of
             C_heap'45'before_632 v6
               -> coe
                    C_heap'45'before_632
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v6) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump
d_AllocBump_876 a0 = ()
data T_AllocBump_876 = C_mkBump_886 Integer Integer
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-slot-delta
d_next'45'slot'45'delta_882 :: T_AllocBump_876 -> Integer
d_next'45'slot'45'delta_882 v0
  = case coe v0 of
      C_mkBump_886 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_884 :: T_AllocBump_876 -> Integer
d_next'45'heap'45'ref'45'delta_884 v0
  = case coe v0 of
      C_mkBump_886 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump
d_apply'45'bump_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_apply'45'bump_888 ~v0 v1 v2 = du_apply'45'bump_888 v1 v2
du_apply'45'bump_888 ::
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
du_apply'45'bump_888 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v1))
      (coe
         addInt (coe d_next'45'slot'45'delta_882 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_884 (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
            (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-0
d_bump'45'0_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876
d_bump'45'0_894 ~v0 = du_bump'45'0_894
du_bump'45'0_894 :: T_AllocBump_876
du_bump'45'0_894
  = coe C_mkBump_886 (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Machine.Allocation.FrontierInvariant.bump-+
d_bump'45''43'_896 ::
  T_AllocBump_876 -> T_AllocBump_876 -> T_AllocBump_876
d_bump'45''43'_896 v0 v1
  = coe
      C_mkBump_886
      (coe
         addInt (coe d_next'45'slot'45'delta_882 (coe v0))
         (coe d_next'45'slot'45'delta_882 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_884 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_884 (coe v1)))
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_906 ::
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_906 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-compose
d_apply'45'bump'45'compose_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876 ->
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_914 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant._.compose-eq
d_compose'45'eq_932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876 ->
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'eq_932 = erased
-- Once.CCC.Machine.Allocation.FrontierInvariant.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_948 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_948 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump
d_AllocBump_980 a0 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.BeforeFrontier
d_BeforeFrontier_984 a0 a1 a2 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.StackAncestorSource
d_StackAncestorSource_986 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump
d_apply'45'bump_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_apply'45'bump_988 ~v0 = du_apply'45'bump_988
du_apply'45'bump_988 ::
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
du_apply'45'bump_988 = coe du_apply'45'bump_888
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-0-eq
d_apply'45'bump'45'0'45'eq_990 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'0'45'eq_990 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-compose
d_apply'45'bump'45'compose_992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876 ->
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'compose_992 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.apply-bump-preserves-frame
d_apply'45'bump'45'preserves'45'frame_994 ::
  T_AllocBump_876 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'bump'45'preserves'45'frame_994 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.before-frontier-stack-disjoint
d_before'45'frontier'45'stack'45'disjoint_996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  Integer ->
  T_BeforeFrontier_610 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_before'45'frontier'45'stack'45'disjoint_996 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.bump-+
d_bump'45''43'_998 ::
  T_AllocBump_876 -> T_AllocBump_876 -> T_AllocBump_876
d_bump'45''43'_998 v0 v1
  = coe
      C_mkBump_886
      (coe
         addInt (coe d_next'45'slot'45'delta_882 (coe v0))
         (coe d_next'45'slot'45'delta_882 (coe v1)))
      (coe
         addInt (coe d_next'45'heap'45'ref'45'delta_884 (coe v0))
         (coe d_next'45'heap'45'ref'45'delta_884 (coe v1)))
-- Once.CCC.Machine.Allocation.FrameOps._.bump-0
d_bump'45'0_1000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocBump_876
d_bump'45'0_1000 ~v0 = du_bump'45'0_1000
du_bump'45'0_1000 :: T_AllocBump_876
du_bump'45'0_1000 = coe du_bump'45'0_894
-- Once.CCC.Machine.Allocation.FrameOps._.fresh-stack-after
d_fresh'45'stack'45'after_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fresh'45'stack'45'after_1002 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.frontier-monotone
d_frontier'45'monotone_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_frontier'45'monotone_1004 ~v0 = du_frontier'45'monotone_1004
du_frontier'45'monotone_1004 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_frontier'45'monotone_1004 v0 v1 v2 v3 v4 v5 v6
  = coe du_frontier'45'monotone_814 v3 v4 v5 v6
-- Once.CCC.Machine.Allocation.FrameOps._.heap-alloc-advances
d_heap'45'alloc'45'advances_1006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_heap'45'alloc'45'advances_1006 ~v0
  = du_heap'45'alloc'45'advances_1006
du_heap'45'alloc'45'advances_1006 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_heap'45'alloc'45'advances_1006
  = coe du_heap'45'alloc'45'advances_780
-- Once.CCC.Machine.Allocation.FrameOps._.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1012 :: T_AllocBump_876 -> Integer
d_next'45'heap'45'ref'45'delta_1012 v0
  = coe d_next'45'heap'45'ref'45'delta_884 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.next-slot-delta
d_next'45'slot'45'delta_1014 :: T_AllocBump_876 -> Integer
d_next'45'slot'45'delta_1014 v0
  = coe d_next'45'slot'45'delta_882 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.stack-alloc-advances
d_stack'45'alloc'45'advances_1020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_stack'45'alloc'45'advances_1020 ~v0
  = du_stack'45'alloc'45'advances_1020
du_stack'45'alloc'45'advances_1020 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_stack'45'alloc'45'advances_1020 v0 v1 v2 v3
  = coe du_stack'45'alloc'45'advances_744 v0 v2 v3
-- Once.CCC.Machine.Allocation.FrameOps._.≺⇒≢
d_'8826''8658''8802'_1026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''8658''8802'_1026 = erased
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-heap-ref-delta
d_next'45'heap'45'ref'45'delta_1030 :: T_AllocBump_876 -> Integer
d_next'45'heap'45'ref'45'delta_1030 v0
  = coe d_next'45'heap'45'ref'45'delta_884 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps._.AllocBump.next-slot-delta
d_next'45'slot'45'delta_1032 :: T_AllocBump_876 -> Integer
d_next'45'slot'45'delta_1032 v0
  = coe d_next'45'slot'45'delta_882 (coe v0)
-- Once.CCC.Machine.Allocation.FrameOps.push-frame
d_push'45'frame_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_push'45'frame_1054 ~v0 v1 v2 ~v3 = du_push'45'frame_1054 v1 v2
du_push'45'frame_1054 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
du_push'45'frame_1054 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586 (coe v1)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.pop-frame
d_pop'45'frame_1066 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
d_pop'45'frame_1066 ~v0 v1 v2 v3 = du_pop'45'frame_1066 v1 v2 v3
du_pop'45'frame_1066 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522
du_pop'45'frame_1066 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_586
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
         (coe v0))
-- Once.CCC.Machine.Allocation.FrameOps.in-parent-frame-before-child
d_in'45'parent'45'frame'45'before'45'child_1082 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
d_in'45'parent'45'frame'45'before'45'child_1082 v0 ~v1 ~v2 ~v3 v4
                                                v5
  = du_in'45'parent'45'frame'45'before'45'child_1082 v0 v4 v5
du_in'45'parent'45'frame'45'before'45'child_1082 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
du_in'45'parent'45'frame'45'before'45'child_1082 v0 v1 v2
  = coe
      C_stack'45'ancestor_628
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v0))
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v0))
      v1 (coe C_src'45'origin_598 v2)
-- Once.CCC.Machine.Allocation.FrameOps.heap-before-child
d_heap'45'before'45'child_1104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
d_heap'45'before'45'child_1104 ~v0 ~v1 ~v2 ~v3 v4
  = du_heap'45'before'45'child_1104 v4
du_heap'45'before'45'child_1104 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
du_heap'45'before'45'child_1104 v0 = coe C_heap'45'before_632 v0
-- Once.CCC.Machine.Allocation.FrameOps.ancestor-frame-before-child
d_ancestor'45'frame'45'before'45'child_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_610
d_ancestor'45'frame'45'before'45'child_1130 v0 v1 v2 ~v3 v4 ~v5 v6
                                            v7 v8 v9
  = du_ancestor'45'frame'45'before'45'child_1130
      v0 v1 v2 v4 v6 v7 v8 v9
du_ancestor'45'frame'45'before'45'child_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> AgdaAny -> T_BeforeFrontier_610
du_ancestor'45'frame'45'before'45'child_1130 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      C_stack'45'ancestor_628
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
         (coe v1))
      v4
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_94 v0 v2
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
            (coe v1))
         v3 v6 v7)
      (coe C_src'45'above'45'origin_606 v7 v5)
-- Once.CCC.Machine.Allocation.FrameOps.parent-before-child
d_parent'45'before'45'child_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  AgdaAny -> T_BeforeFrontier_610 -> T_BeforeFrontier_610
d_parent'45'before'45'child_1158 v0 v1 v2 ~v3 v4 v5 v6
  = du_parent'45'before'45'child_1158 v0 v1 v2 v4 v5 v6
du_parent'45'before'45'child_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  AgdaAny -> T_BeforeFrontier_610 -> T_BeforeFrontier_610
du_parent'45'before'45'child_1158 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtStack_72 v6 v7
        -> case coe v5 of
             C_stack'45'before_618 v11
               -> coe
                    C_stack'45'ancestor_628
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
                       (coe v1))
                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_582 (coe v1))
                    v4 (coe C_src'45'origin_598 v11)
             C_stack'45'ancestor_628 v10 v11 v12 v13
               -> case coe v13 of
                    C_src'45'origin_598 v16
                      -> coe
                           C_stack'45'ancestor_628
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_94 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_606 v12 v16)
                    C_src'45'above'45'origin_606 v16 v18
                      -> coe
                           C_stack'45'ancestor_628
                           (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
                              (coe v1))
                           v11
                           (coe
                              MAlonzo.Code.Once.CCC.FrameSemantics.d_'8826''45'trans_94 v0 v2
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_580
                                 (coe v1))
                              v6 v4 v12)
                           (coe C_src'45'above'45'origin_606 v12 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_AtDynamic_74 v6
        -> case coe v5 of
             C_heap'45'before_632 v8 -> coe C_heap'45'before_632 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Allocation.FrameOps.pop-preserves-before
d_pop'45'preserves'45'before_1230 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
d_pop'45'preserves'45'before_1230 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'preserves'45'before_1230 v4
du_pop'45'preserves'45'before_1230 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
du_pop'45'preserves'45'before_1230 v0
  = coe C_stack'45'before_618 v0
-- Once.CCC.Machine.Allocation.FrameOps.pop-heap-before
d_pop'45'heap'45'before_1250 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
d_pop'45'heap'45'before_1250 ~v0 ~v1 ~v2 ~v3 v4
  = du_pop'45'heap'45'before_1250 v4
du_pop'45'heap'45'before_1250 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_BeforeFrontier_610
du_pop'45'heap'45'before_1250 v0 = coe C_heap'45'before_632 v0
