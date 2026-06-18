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

module MAlonzo.Code.Once.CCC.Machine.WriteOps where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress

-- Once.CCC.Machine.WriteOps.WriteWithDisjoint._.readLoc
d_readLoc_16 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78
d_readLoc_16 ~v0 = du_readLoc_16
du_readLoc_16 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_78
du_readLoc_16
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_630
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint._.write-loc
d_write'45'loc_54 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468
d_write'45'loc_54 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Allocation.d_write'45'loc_302
      (coe v0)
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint._.BeforeFrontier
d_BeforeFrontier_68 a0 a1 a2 = ()
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.write-preserves-disjoint
d_write'45'preserves'45'disjoint_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'preserves'45'disjoint_164 = erased
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.write-read-same-stack
d_write'45'read'45'same'45'stack_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'read'45'same'45'stack_300 = erased
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.write-read-same-heap
d_write'45'read'45'same'45'heap_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'read'45'same'45'heap_316 = erased
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.ValidWrite
d_ValidWrite_342 a0 a1 a2 = ()
data T_ValidWrite_342 = C_stack'45'valid_350 | C_heap'45'valid_356
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.write-read-same
d_write'45'read'45'same_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  T_ValidWrite_342 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'read'45'same_364 = erased
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.write-at-frontier-preserves-before
d_write'45'at'45'frontier'45'preserves'45'before_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'at'45'frontier'45'preserves'45'before_388 = erased
-- Once.CCC.Machine.WriteOps.WriteWithDisjoint.write-at-suc-frontier-preserves-before
d_write'45'at'45'suc'45'frontier'45'preserves'45'before_512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_468 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_522 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_ValueLocation_68 ->
  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_610 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_write'45'at'45'suc'45'frontier'45'preserves'45'before_512
  = erased
