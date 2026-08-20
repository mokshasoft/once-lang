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

module MAlonzo.Code.Once.CCC.Machine.SMCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Allocator.AbstractInstance
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Machine.SMCore.HeapRegion
d_HeapRegion_16 = ()
data T_HeapRegion_16
  = C_heap'45'region_26 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
                        Integer
-- Once.CCC.Machine.SMCore.HeapRegion.region-ref
d_region'45'ref_22 ::
  T_HeapRegion_16 -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_region'45'ref_22 v0
  = case coe v0 of
      C_heap'45'region_26 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapRegion.region-size
d_region'45'size_24 :: T_HeapRegion_16 -> Integer
d_region'45'size_24 v0
  = case coe v0 of
      C_heap'45'region_26 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.InRegion
d_InRegion_28 a0 a1 = ()
newtype T_InRegion_28
  = C_in'45'region_36 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.SMCore.HeapOwnership
d_HeapOwnership_38 :: ()
d_HeapOwnership_38 = erased
-- Once.CCC.Machine.SMCore.OutsideOwned
d_OutsideOwned_40 a0 a1 = ()
data T_OutsideOwned_40
  = C_outside'45'nil_44 |
    C_outside'45'cons_52 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                         T_OutsideOwned_40
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_54 = ()
data T_AbstractReg_54
  = C_Input1_56 | C_Output_58 | C_Scratch_60 | C_Count_62
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_66 a0 = ()
data T_StoredValue_66
  = C_SV'45'Ptr_70 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_SV'45'Tag_72 Integer |
    C_SV'45'Lit_76 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_SV'45'Code_78 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_82 ~v0 v1 = du_sucLoc_82 v1
du_sucLoc_82 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_82 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v1 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 (coe v1)
             (coe addInt (coe (1 :: Integer)) (coe v2))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v1
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
             (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_offsetLoc_92 ~v0 v1 v2 = du_offsetLoc_92 v1 v2
du_offsetLoc_92 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_offsetLoc_92 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 (coe v2)
             (coe addInt (coe v1) (coe v3))
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
             (coe
                MAlonzo.Code.Once.Memory.HeapAddress.d_offsetHL_98 (coe v2)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_106 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_HeapMem_112 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__120 ::
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__120 v0 v1
  = case coe v0 of
      C_Input1_56
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_58
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Scratch_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Scratch_60
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Count_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Count_62
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_124 a0 = ()
data T_Registers_124
  = C_mkRegs_144 T_StoredValue_66 T_StoredValue_66 T_StoredValue_66
                 T_StoredValue_66
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_136 :: T_Registers_124 -> T_StoredValue_66
d_input1_136 v0
  = case coe v0 of
      C_mkRegs_144 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_138 :: T_Registers_124 -> T_StoredValue_66
d_output_138 v0
  = case coe v0 of
      C_mkRegs_144 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.scratch
d_scratch_140 :: T_Registers_124 -> T_StoredValue_66
d_scratch_140 v0
  = case coe v0 of
      C_mkRegs_144 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.count
d_count_142 :: T_Registers_124 -> T_StoredValue_66
d_count_142 v0
  = case coe v0 of
      C_mkRegs_144 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 -> T_AbstractReg_54 -> T_StoredValue_66
d_readReg_148 ~v0 v1 v2 = du_readReg_148 v1 v2
du_readReg_148 ::
  T_Registers_124 -> T_AbstractReg_54 -> T_StoredValue_66
du_readReg_148 v0 v1
  = case coe v1 of
      C_Input1_56 -> coe d_input1_136 (coe v0)
      C_Output_58 -> coe d_output_138 (coe v0)
      C_Scratch_60 -> coe d_scratch_140 (coe v0)
      C_Count_62 -> coe d_count_142 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 -> T_StoredValue_66 -> T_Registers_124
d_writeReg_160 ~v0 v1 v2 = du_writeReg_160 v1 v2
du_writeReg_160 ::
  T_Registers_124 ->
  T_AbstractReg_54 -> T_StoredValue_66 -> T_Registers_124
du_writeReg_160 v0 v1
  = case coe v1 of
      C_Input1_56
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_144 (coe v2) (coe d_output_138 (coe v0))
                  (coe d_scratch_140 (coe v0)) (coe d_count_142 (coe v0)))
      C_Output_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_144 (coe d_input1_136 (coe v0)) (coe v2)
                  (coe d_scratch_140 (coe v0)) (coe d_count_142 (coe v0)))
      C_Scratch_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_144 (coe d_input1_136 (coe v0))
                  (coe d_output_138 (coe v0)) (coe v2) (coe d_count_142 (coe v0)))
      C_Count_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_144 (coe d_input1_136 (coe v0))
                  (coe d_output_138 (coe v0)) (coe d_scratch_140 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_192 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_314 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_342 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_368 = ()
data T_RegOp_368
  = C_scratch'45'one_370 | C_scratch'45'zero_372 |
    C_scratch'45'dec_374 | C_scratch'45'load'45'count_376 |
    C_count'45'zero_378 | C_count'45'inc_380
-- Once.CCC.Machine.SMCore.sv-succ
d_sv'45'succ_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'succ_384 ~v0 v1 = du_sv'45'succ_384 v1
du_sv'45'succ_384 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'succ_384 v0
  = let v1 = coe C_SV'45'Tag_72 (coe (1 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_72 v2
           -> coe C_SV'45'Tag_72 (coe addInt (coe (1 :: Integer)) (coe v2))
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-pred
d_sv'45'pred_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'pred_390 ~v0 v1 = du_sv'45'pred_390 v1
du_sv'45'pred_390 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'pred_390 v0
  = let v1 = coe C_SV'45'Tag_72 (coe (0 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_72 v2
           -> case coe v2 of
                _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                    let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                    coe (coe C_SV'45'Tag_72 (coe v3))
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-tag-val
d_sv'45'tag'45'val_396 :: T_StoredValue_66 -> Integer
d_sv'45'tag'45'val_396 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_SV'45'Tag_72 v2 -> coe v2
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.LocState
d_LocState_402 a0 = ()
data T_LocState_402
  = C_mkLocState_422 T_Registers_124
                     (AgdaAny -> Integer -> Maybe T_StoredValue_66)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_66)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_414 :: T_LocState_402 -> T_Registers_124
d_regs_414 v0
  = case coe v0 of
      C_mkLocState_422 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_416 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_stackMem_416 v0
  = case coe v0 of
      C_mkLocState_422 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_418 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_heapMem_418 v0
  = case coe v0 of
      C_mkLocState_422 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_420 :: T_LocState_402 -> Bool
d_halted_420 v0
  = case coe v0 of
      C_mkLocState_422 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_368 -> T_Registers_124 -> T_Registers_124
d_setReg_426 ~v0 v1 v2 = du_setReg_426 v1 v2
du_setReg_426 :: T_RegOp_368 -> T_Registers_124 -> T_Registers_124
du_setReg_426 v0 v1
  = case coe v0 of
      C_scratch'45'one_370
        -> coe
             du_writeReg_160 v1 (coe C_Scratch_60)
             (coe C_SV'45'Tag_72 (coe (1 :: Integer)))
      C_scratch'45'zero_372
        -> coe
             du_writeReg_160 v1 (coe C_Scratch_60)
             (coe C_SV'45'Tag_72 (coe (0 :: Integer)))
      C_scratch'45'dec_374
        -> coe
             du_writeReg_160 v1 (coe C_Scratch_60)
             (coe
                du_sv'45'pred_390 (coe du_readReg_148 (coe v1) (coe C_Scratch_60)))
      C_scratch'45'load'45'count_376
        -> coe
             du_writeReg_160 v1 (coe C_Scratch_60)
             (coe du_readReg_148 (coe v1) (coe C_Count_62))
      C_count'45'zero_378
        -> coe
             du_writeReg_160 v1 (coe C_Count_62)
             (coe C_SV'45'Tag_72 (coe (0 :: Integer)))
      C_count'45'inc_380
        -> coe
             du_writeReg_160 v1 (coe C_Count_62)
             (coe
                du_sv'45'succ_384 (coe du_readReg_148 (coe v1) (coe C_Count_62)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_368 -> T_LocState_402 -> T_LocState_402
d_exec'45'reg'45'op_442 ~v0 v1 v2 = du_exec'45'reg'45'op_442 v1 v2
du_exec'45'reg'45'op_442 ::
  T_RegOp_368 -> T_LocState_402 -> T_LocState_402
du_exec'45'reg'45'op_442 v0 v1
  = coe
      C_mkLocState_422
      (coe du_setReg_426 (coe v0) (coe d_regs_414 (coe v1)))
      (coe d_stackMem_416 (coe v1)) (coe d_heapMem_418 (coe v1))
      (coe d_halted_420 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_448 = ()
data T_AllocMode_448 = C_Stack_450 | C_Heap_452
-- Once.CCC.Machine.SMCore.size-with-aux
d_size'45'with'45'aux_460 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_size'45'with'45'aux_460 v0 v1 ~v2 v3 v4
  = du_size'45'with'45'aux_460 v0 v1 v3 v4
du_size'45'with'45'aux_460 ::
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_size'45'with'45'aux_460 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe v0)
             else coe seq (coe v5) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.size-with
d_size'45'with_476 ::
  Integer -> Integer -> (Integer -> Integer) -> Integer -> Integer
d_size'45'with_476 v0 v1 v2 v3
  = coe
      du_size'45'with'45'aux_460 (coe v0) (coe v3) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v1))
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_488 a0 = ()
data T_AllocState_488
  = C_mkAllocState_584 AgdaAny
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer Integer Integer
                       (Integer -> Integer)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_572 :: T_AllocState_488 -> AgdaAny
d_current'45'frame_572 v0
  = case coe v0 of
      C_mkAllocState_584 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_574 ::
  T_AllocState_488 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_574 v0
  = case coe v0 of
      C_mkAllocState_584 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.frame-slots
d_frame'45'slots_576 :: T_AllocState_488 -> Integer
d_frame'45'slots_576 v0
  = case coe v0 of
      C_mkAllocState_584 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_578 :: T_AllocState_488 -> Integer
d_next'45'slot_578 v0
  = case coe v0 of
      C_mkAllocState_584 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_580 :: T_AllocState_488 -> Integer
d_next'45'heap'45'ref_580 v0
  = case coe v0 of
      C_mkAllocState_584 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_582 :: T_AllocState_488 -> Integer -> Integer
d_block'45'size_582 v0
  = case coe v0 of
      C_mkAllocState_584 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_624 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_624 v0 v1 v2 = coe d_stackMem_416 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_632 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_632 v0 v1 = coe d_heapMem_418 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_638 ~v0 v1 v2 = du_readLoc_638 v1 v2
du_readLoc_638 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_638 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_416 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_418 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_658 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_658 v5 v6 v7 v8
du_writeStackMem'45'aux_658 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_658 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3))
                              else coe seq (coe v7) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem
d_writeStackMem_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_666 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_658
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__86 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_688 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_clear'45'frame'45'aux_688 v5 v6 v7
du_clear'45'frame'45'aux_688 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_688 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              else coe seq (coe v6) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.clear-frame
d_clear'45'frame_694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_694 v0 v1 v2 v3 v4 v5
  = coe
      du_clear'45'frame'45'aux_688
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__86 v0 v2 v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v5)
         (coe v3))
      (coe v1 v4 v5)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-just
d_clear'45'frame'45'just_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_718 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_770 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_770 v3 v4 v5
du_writeHeapMem'45'aux_770 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_770 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_776 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_776 v1 v2 v3 v4
du_writeHeapMem_776 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_776 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_770
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_786 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_422 (coe d_regs_414 (coe v1))
      (coe
         d_writeStackMem_666 (coe v0) (coe d_stackMem_416 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_418 (coe v1)) (coe d_halted_420 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_796 ~v0 v1 v2 v3 = du_writeLocToHeap_796 v1 v2 v3
du_writeLocToHeap_796 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_796 v0 v1 v2
  = coe
      C_mkLocState_422 (coe d_regs_414 (coe v0))
      (coe d_stackMem_416 (coe v0))
      (coe
         du_writeHeapMem_776 (coe d_heapMem_418 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_420 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_804 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_804 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_786 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_70 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_796 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_72 v5
               -> coe du_writeLocToHeap_796 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_76 v5 v6 v7
               -> coe du_writeLocToHeap_796 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_78 v5
               -> coe du_writeLocToHeap_796 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_854 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_892 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_932 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_932 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_952 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_952 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_980 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1012 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1290 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1342 a0 = ()
data T_LocSourceExt_1342
  = C_Loc_1346 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1348 T_AbstractReg_54 | C_IndRegSuc_1350 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1354 ~v0 v1 = du_sv'45'as'45'loc_1354 v1
du_sv'45'as'45'loc_1354 ::
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1354 v0
  = case coe v0 of
      C_SV'45'Ptr_70 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_SV'45'Tag_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Lit_76 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Code_78 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_LocSourceExt_1342 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1360 ~v0 v1 v2 = du_resolveSourceExt_1360 v1 v2
du_resolveSourceExt_1360 ::
  T_Registers_124 ->
  T_LocSourceExt_1342 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1360 v0 v1
  = case coe v1 of
      C_Loc_1346 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1348 v2
        -> coe
             du_sv'45'as'45'loc_1354 (coe du_readReg_148 (coe v0) (coe v2))
      C_IndRegSuc_1350 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1354 (coe du_readReg_148 (coe v0) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe du_sucLoc_82 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1390 a0 = ()
data T_Instr_1390
  = C_load_1394 T_AbstractReg_54 T_LocSourceExt_1342 |
    C_store_1396 T_LocSourceExt_1342 T_AbstractReg_54 |
    C_mov_1398 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_1406 v0 = coe d_clear'45'frame_694 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_1408 ~v0 = du_clear'45'frame'45'aux_1408
du_clear'45'frame'45'aux_1408 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_1408 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_688 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1410 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1412 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1412 v0 v1 = coe d_heapMem_418 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1414 ~v0 = du_readLoc_1414
du_readLoc_1414 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1414 = coe du_readLoc_638
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1416 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1416 v0 v1 v2 = coe d_stackMem_416 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1418 ~v0 = du_writeHeapMem_1418
du_writeHeapMem_1418 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1418 = coe du_writeHeapMem_776
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1420 ~v0 = du_writeHeapMem'45'aux_1420
du_writeHeapMem'45'aux_1420 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1420 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_770 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_1422 v0 = coe d_writeLoc_804 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1424 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1426 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1426 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1428 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1430 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1432 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1434 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1436 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1436 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_1438 ~v0 = du_writeLocToHeap_1438
du_writeLocToHeap_1438 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_1438 = coe du_writeLocToHeap_796
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_1440 v0 = coe d_writeLocToStack_786 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1442 v0 = coe d_writeStackMem_666 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1444 ~v0 = du_writeStackMem'45'aux_1444
du_writeStackMem'45'aux_1444 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1444 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_658 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'load'45'with'45'value_1446 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1446 v1 v2
du_exec'45'load'45'with'45'value_1446 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
du_exec'45'load'45'with'45'value_1446 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_422 (coe du_writeReg_160 (d_regs_414 (coe v3)) v0 v2)
                  (coe d_stackMem_416 (coe v3)) (coe d_heapMem_418 (coe v3))
                  (coe d_halted_420 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_422 (coe d_regs_414 (coe v2))
                  (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'via'45'resolved_1458 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1458 v1 v2
du_exec'45'load'45'via'45'resolved_1458 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'via'45'resolved_1458 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1446 v0
                  (coe du_readLoc_638 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_422 (coe d_regs_414 (coe v2))
                  (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'via'45'resolved_1470 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_804 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_422 (coe d_regs_414 (coe v3))
                  (coe d_stackMem_416 (coe v3)) (coe d_heapMem_418 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1480 ~v0 v1 = du_slot'45'base_1480 v1
du_slot'45'base_1480 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1480 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1354 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
d_exec'45'lea'45'indexed'45'via_1484 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1484 v1
du_exec'45'lea'45'indexed'45'via_1484 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
du_exec'45'lea'45'indexed'45'via_1484 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_422
                  (coe
                     du_writeReg_160 (d_regs_414 (coe v3)) (coe C_Input1_56)
                     (coe C_SV'45'Ptr_70 (coe du_offsetLoc_92 (coe v1) (coe v2))))
                  (coe d_stackMem_416 (coe v3)) (coe d_heapMem_418 (coe v3))
                  (coe d_halted_420 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_422 (coe d_regs_414 (coe v2))
                  (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_1496 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1496 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1496 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_1496 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1446 v0
                  (coe du_readLoc_638 (coe v3) (coe du_sucLoc_82 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_422 (coe d_regs_414 (coe v2))
                  (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_1508 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_804
                  (coe v0) (coe v4) (coe du_sucLoc_82 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_422 (coe d_regs_414 (coe v3))
                  (coe d_stackMem_416 (coe v3)) (coe d_heapMem_418 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1390 -> T_LocState_402 -> T_LocState_402
d_exec_1518 v0 v1
  = case coe v1 of
      C_load_1394 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1458 v2
                  (coe du_resolveSourceExt_1360 (coe d_regs_414 (coe v4)) (coe v3))
                  v4)
      C_store_1396 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1470 v0
                  (coe du_resolveSourceExt_1360 (coe d_regs_414 (coe v4)) (coe v2))
                  (coe du_readReg_148 (coe d_regs_414 (coe v4)) (coe v3)) v4)
      C_mov_1398 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_422
                  (coe
                     du_writeReg_160 (d_regs_414 (coe v4)) v2
                     (coe du_readReg_148 (coe d_regs_414 (coe v4)) (coe v3)))
                  (coe d_stackMem_416 (coe v4)) (coe d_heapMem_418 (coe v4))
                  (coe d_halted_420 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1544 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1550 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1390] -> T_LocState_402 -> T_LocState_402
d_execList_1552 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_420 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1552 (coe v0) (coe v4) (coe d_exec_1518 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_1584 v0 = coe d_clear'45'frame_694 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_1586 ~v0 = du_clear'45'frame'45'aux_1586
du_clear'45'frame'45'aux_1586 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_1586 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_688 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1588 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1590 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1590 v0 v1 = coe d_heapMem_418 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1592 ~v0 = du_readLoc_1592
du_readLoc_1592 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1592 = coe du_readLoc_638
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1594 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1594 v0 v1 v2 = coe d_stackMem_416 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1596 ~v0 = du_writeHeapMem_1596
du_writeHeapMem_1596 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1596 = coe du_writeHeapMem_776
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1598 ~v0 = du_writeHeapMem'45'aux_1598
du_writeHeapMem'45'aux_1598 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1598 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_770 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_1600 v0 = coe d_writeLoc_804 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1602 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1604 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1604 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1606 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1608 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1610 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1612 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1614 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1614 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_1616 ~v0 = du_writeLocToHeap_1616
du_writeLocToHeap_1616 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_1616 = coe du_writeLocToHeap_796
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_1618 v0 = coe d_writeLocToStack_786 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1620 v0 = coe d_writeStackMem_666 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1622 ~v0 = du_writeStackMem'45'aux_1622
du_writeStackMem'45'aux_1622 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1622 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_658 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1390 -> T_LocState_402 -> T_LocState_402
d_exec_1626 v0 = coe d_exec_1518 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
d_exec'45'lea'45'indexed'45'via_1628 ~v0
  = du_exec'45'lea'45'indexed'45'via_1628
du_exec'45'lea'45'indexed'45'via_1628 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
du_exec'45'lea'45'indexed'45'via_1628
  = coe du_exec'45'lea'45'indexed'45'via_1484
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1630 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1632 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_1634 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1634
du_exec'45'load'45'suc'45'via'45'resolved_1634 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_1634
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1496
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'via'45'resolved_1636 ~v0
  = du_exec'45'load'45'via'45'resolved_1636
du_exec'45'load'45'via'45'resolved_1636 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'via'45'resolved_1636
  = coe du_exec'45'load'45'via'45'resolved_1458
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'load'45'with'45'value_1638 ~v0
  = du_exec'45'load'45'with'45'value_1638
du_exec'45'load'45'with'45'value_1638 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
du_exec'45'load'45'with'45'value_1638
  = coe du_exec'45'load'45'with'45'value_1446
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_1640 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1508 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'via'45'resolved_1642 v0
  = coe d_exec'45'store'45'via'45'resolved_1470 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1390] -> T_LocState_402 -> T_LocState_402
d_execList_1644 v0 = coe d_execList_1552 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1646 ~v0 = du_slot'45'base_1646
du_slot'45'base_1646 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1646 = coe du_slot'45'base_1480
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_LocSourceExt_1342 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_1648 ~v0 v1 v2
  = du_resolved'45'readLoc_1648 v1 v2
du_resolved'45'readLoc_1648 ::
  T_LocState_402 -> T_LocSourceExt_1342 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_1648 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1360 (coe d_regs_414 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_638 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1678 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1748 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1824 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1854 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1910 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1962 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2014 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2030 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2048 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2062 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2080 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2146 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2170 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2198 = ()
data T_FlatCtrl_2198
  = C_c'45'label_2200 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2202 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'scratch'45'zero_2204 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2206 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'thunk_2208 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 Integer |
    C_c'45'ret_2210 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2212 = ()
data T_AbstractInstr_2212
  = C_mov'45'to'45'output_2214 | C_mov'45'to'45'input_2216 |
    C_load'45'indirect_2218 | C_load'45'indirect'45'suc_2220 |
    C_load'45'from'45'slot_2222 Integer |
    C_store'45'at'45'slot_2224 Integer | C_store'45'indirect_2226 |
    C_store'45'indirect'45'suc_2228 | C_lea'45'slot_2230 Integer |
    C_restore'45'input_2232 Integer |
    C_instr'45'alloc'45'stack_2234 Integer |
    C_instr'45'dealloc'45'stack_2236 Integer |
    C_instr'45'reclaim'45'to_2238 Integer |
    C_instr'45'push'45'frame_2240 Integer |
    C_instr'45'pop'45'frame_2242 | C_instr'45'call'45'closure_2244 |
    C_worklist'45'init_2246 Integer | C_worklist'45'push_2248 Integer |
    C_worklist'45'pop_2250 Integer | C_worklist'45'check_2252 Integer |
    C_instr'45'sigop_2258 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 |
    C_instr'45'load'45'const_2264 MAlonzo.Code.Once.Type.T_Type_112
                                  MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_instr'45'load'45'code'45'addr_2266 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2268 |
    C_instr'45'load'45'tag'45'lit_2270 Integer |
    C_instr'45'case'45'on'45'tag_2272 [T_AbstractInstr_2212]
                                      [T_AbstractInstr_2212] |
    C_instr'45'alloc'45'heap_2274 Integer |
    C_instr'45'loop_2276 [T_AbstractInstr_2212] |
    C_instr'45'reg'45'op_2278 T_RegOp_368 |
    C_instr'45'ctrl_2280 T_FlatCtrl_2198 |
    C_lea'45'indexed_2282 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2284 :: ()
d_AbstractTrace_2284 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2286 = ()
data T_TreeTrace_2286
  = C_ε_2288 | C_instr_2290 T_AbstractInstr_2212 |
    C__'9656'__2292 T_TreeTrace_2286 T_TreeTrace_2286 |
    C_branch_2294 Integer T_TreeTrace_2286 T_TreeTrace_2286 |
    C_call'45'sub_2296 T_TreeTrace_2286 |
    C_flat_2298 [T_AbstractInstr_2212]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2300 :: [T_AbstractInstr_2212] -> T_TreeTrace_2286
d_flatToTree_2300 v0
  = case coe v0 of
      [] -> coe C_ε_2288
      (:) v1 v2
        -> coe
             C__'9656'__2292 (coe C_instr_2290 (coe v1))
             (coe d_flatToTree_2300 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2306 :: T_TreeTrace_2286 -> [T_AbstractInstr_2212]
d_treeToFlat_2306 v0
  = case coe v0 of
      C_ε_2288 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2290 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2292 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2306 (coe v1)) (coe d_treeToFlat_2306 (coe v2))
      C_branch_2294 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2306 (coe v2)) (coe d_treeToFlat_2306 (coe v3))
      C_call'45'sub_2296 v1 -> coe d_treeToFlat_2306 (coe v1)
      C_flat_2298 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2322 ::
  Integer -> T_TreeTrace_2286 -> [T_AbstractInstr_2212]
d_treeToRunnable_2322 v0 v1
  = case coe v1 of
      C_ε_2288 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2290 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2292 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2322 (coe v0) (coe v2))
             (coe d_treeToRunnable_2322 (coe v0) (coe v3))
      C_branch_2294 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2322 (coe v0) (coe v3))
             (coe d_treeToRunnable_2322 (coe v0) (coe v4))
      C_call'45'sub_2296 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2248 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2322 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2250 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2298 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2352 ::
  Integer -> T_TreeTrace_2286 -> [T_AbstractInstr_2212]
d_treeToRunnableWithInit_2352 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2246 (coe v0))
      (coe d_treeToRunnable_2322 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_2398 v0 = coe d_clear'45'frame_694 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_2400 ~v0 = du_clear'45'frame'45'aux_2400
du_clear'45'frame'45'aux_2400 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_2400 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_688 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2402 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2404 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_2404 v0 v1 = coe d_heapMem_418 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_2406 ~v0 = du_readLoc_2406
du_readLoc_2406 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_2406 = coe du_readLoc_638
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2408 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_2408 v0 v1 v2 = coe d_stackMem_416 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_2410 ~v0 = du_writeHeapMem_2410
du_writeHeapMem_2410 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_2410 = coe du_writeHeapMem_776
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_2412 ~v0 = du_writeHeapMem'45'aux_2412
du_writeHeapMem'45'aux_2412 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_2412 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_770 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_2414 v0 = coe d_writeLoc_804 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2416 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2418 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2418 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2420 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2422 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2424 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2426 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2428 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2428 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_2430 ~v0 = du_writeLocToHeap_2430
du_writeLocToHeap_2430 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_2430 = coe du_writeLocToHeap_796
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_2432 v0 = coe d_writeLocToStack_786 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_2434 v0 = coe d_writeStackMem_666 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_2436 ~v0 = du_writeStackMem'45'aux_2436
du_writeStackMem'45'aux_2436 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_2436 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_658 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1390 -> T_LocState_402 -> T_LocState_402
d_exec_2440 v0 = coe d_exec_1518 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
d_exec'45'lea'45'indexed'45'via_2442 ~v0
  = du_exec'45'lea'45'indexed'45'via_2442
du_exec'45'lea'45'indexed'45'via_2442 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
du_exec'45'lea'45'indexed'45'via_2442
  = coe du_exec'45'lea'45'indexed'45'via_1484
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2444 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2446 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_2448 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2448
du_exec'45'load'45'suc'45'via'45'resolved_2448 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_2448
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1496
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'via'45'resolved_2450 ~v0
  = du_exec'45'load'45'via'45'resolved_2450
du_exec'45'load'45'via'45'resolved_2450 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'via'45'resolved_2450
  = coe du_exec'45'load'45'via'45'resolved_1458
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'load'45'with'45'value_2452 ~v0
  = du_exec'45'load'45'with'45'value_2452
du_exec'45'load'45'with'45'value_2452 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
du_exec'45'load'45'with'45'value_2452
  = coe du_exec'45'load'45'with'45'value_1446
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_2454 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1508 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'via'45'resolved_2456 v0
  = coe d_exec'45'store'45'via'45'resolved_1470 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1390] -> T_LocState_402 -> T_LocState_402
d_execList_2458 v0 = coe d_execList_1552 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2460 ~v0 = du_slot'45'base_2460
du_slot'45'base_2460 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2460 = coe du_slot'45'base_1480
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2464 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2466 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2468 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2470 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2472 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2474 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2476 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1342 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2478 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2480 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2482 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2484 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2486 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2488 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_LocSourceExt_1342 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_2490 ~v0 = du_resolved'45'readLoc_2490
du_resolved'45'readLoc_2490 ::
  T_LocState_402 -> T_LocSourceExt_1342 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_2490 = coe du_resolved'45'readLoc_1648
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2492 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2492 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2492 ::
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2492 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe du_writeReg_160 (d_regs_414 (coe v1)) (coe C_Output_58) v3)
                (coe d_stackMem_416 (coe v1)) (coe d_heapMem_418 (coe v1))
                (coe d_halted_420 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422 (coe d_regs_414 (coe v1))
                (coe d_stackMem_416 (coe v1)) (coe d_heapMem_418 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2504 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2504 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2504 ::
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2504 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe du_writeReg_160 (d_regs_414 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_416 (coe v1)) (coe d_heapMem_418 (coe v1))
                (coe d_halted_420 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422 (coe d_regs_414 (coe v1))
                (coe d_stackMem_416 (coe v1)) (coe d_heapMem_418 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2522 ::
  T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2522 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2528 ::
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2528 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2536 ::
  T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2536 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2542 ::
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2542 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66
d_unit'45'storedvalue_2544 ~v0 = du_unit'45'storedvalue_2544
du_unit'45'storedvalue_2544 :: T_StoredValue_66
du_unit'45'storedvalue_2544
  = coe
      C_SV'45'Lit_76 (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2550 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2550 v3 v4
du_combine'45'typed_2550 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2550 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-int
d_readTyped'45'int_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 -> Maybe Integer
d_readTyped'45'int_2556 ~v0 v1 = du_readTyped'45'int_2556 v1
du_readTyped'45'int_2556 :: Maybe T_StoredValue_66 -> Maybe Integer
du_readTyped'45'int_2556 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_198
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-pair
d_readTyped'45'pair_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_2564 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'pair_2564 v3 v4 v5 v6
du_readTyped'45'pair_2564 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2564 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> case coe v5 of
                C_SV'45'Ptr_70 v6
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              C_SV'45'Ptr_70 v8
                                -> coe du_combine'45'typed_2550 (coe v0 v6) (coe v1 v8)
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_66 -> Maybe AgdaAny
d_readReg'45'typed_2580 ~v0 v1 v2 = du_readReg'45'typed_2580 v1 v2
du_readReg'45'typed_2580 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_66 -> Maybe AgdaAny
du_readReg'45'typed_2580 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C_Int_136
           -> case coe v1 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_198
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped
d_readTyped_2586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> Maybe AgdaAny
d_readTyped_2586 ~v0 v1 v2 v3 = du_readTyped_2586 v1 v2 v3
du_readTyped_2586 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> Maybe AgdaAny
du_readTyped_2586 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
           -> coe
                du_readTyped'45'pair_2564
                (coe (\ v6 -> coe du_readTyped_2586 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2586 (coe v5) (coe v6) (coe v2)))
                (coe du_readLoc_638 (coe v2) (coe v1))
                (coe du_readLoc_638 (coe v2) (coe du_sucLoc_82 (coe v1)))
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe
                du_readTyped'45'int_2556 (coe du_readLoc_638 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2616
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_402 -> T_StoredValue_66
d_pure'45'sigop'45'output_2622 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_2644 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v2))
      (coe
         du_sv'45'as'45'loc_1354
         (coe du_readReg_148 (coe d_regs_414 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_66
d_pure'45'sigop'45'out'45'val_2628 ~v0 ~v1 v2 v3 v4 v5
  = du_pure'45'sigop'45'out'45'val_2628 v2 v3 v4 v5
du_pure'45'sigop'45'out'45'val_2628 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_66
du_pure'45'sigop'45'out'45'val_2628 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_SV'45'Lit_76 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.SigOp.Info.du_semM_188 v1 v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2544
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_2644 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pure'45'sigop'45'out'45'val_2628 (coe v2) (coe v3) (coe v7)
                    (coe du_readTyped_2586 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'sigop'45'out'45'val_2628 (coe v2) (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2580 (coe v1)
                       (coe du_readReg_148 (coe d_regs_414 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2616 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_402 -> T_StoredValue_66
d_exec'45'sigop'45'output'45'of_2680 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_pure'45'sigop'45'output_2622 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe du_unit'45'storedvalue_2544
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe du_unit'45'storedvalue_2544
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_402 -> T_StoredValue_66
d_exec'45'sigop'45'output_2690 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2680 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_2700 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2700 v3
du_exec'45'sigop'45'halts'45'of_2700 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> Bool
du_exec'45'sigop'45'halts'45'of_2700 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_2706 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2706 v3
du_exec'45'sigop'45'halts_2706 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 -> Bool
du_exec'45'sigop'45'halts_2706 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2700
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> Maybe T_StoredValue_66
d_case'45'tag'45'at_2712 ~v0 v1 = du_case'45'tag'45'at_2712 v1
du_case'45'tag'45'at_2712 ::
  T_LocState_402 -> Maybe T_StoredValue_66
du_case'45'tag'45'at_2712 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1354
              (coe d_input1_136 (coe d_regs_414 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_638 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.BodyRunner
d_BodyRunner_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_2726 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_2728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_LocState_402 -> T_LocState_402
d_loop'45'reanchor'45'loc_2728 ~v0 v1 v2
  = du_loop'45'reanchor'45'loc_2728 v1 v2
du_loop'45'reanchor'45'loc_2728 ::
  T_LocState_402 -> T_LocState_402 -> T_LocState_402
du_loop'45'reanchor'45'loc_2728 v0 v1
  = coe
      C_mkLocState_422 (coe d_regs_414 (coe v1))
      (coe d_stackMem_416 (coe v0)) (coe d_heapMem_418 (coe v1))
      (coe d_halted_420 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_2734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_488 -> T_AllocState_488 -> T_AllocState_488
d_loop'45'reanchor'45'alloc_2734 ~v0 v1 v2
  = du_loop'45'reanchor'45'alloc_2734 v1 v2
du_loop'45'reanchor'45'alloc_2734 ::
  T_AllocState_488 -> T_AllocState_488 -> T_AllocState_488
du_loop'45'reanchor'45'alloc_2734 v0 v1
  = coe
      C_mkAllocState_584 (coe d_current'45'frame_572 (coe v0))
      (coe d_saved'45'frames_574 (coe v1))
      (coe d_frame'45'slots_576 (coe v1))
      (coe d_next'45'slot_578 (coe v0))
      (coe d_next'45'heap'45'ref_580 (coe v1))
      (coe d_block'45'size_582 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_2740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_402 ->
   T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_2740 ~v0 v1 v2 v3 v4
  = du_exec'45'loop'45'run_2740 v1 v2 v3 v4
du_exec'45'loop'45'run_2740 ::
  (T_LocState_402 ->
   T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_2740 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422 (coe d_regs_414 (coe v2))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_420 (coe v2) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                   else (let v6 = d_scratch_140 (coe d_regs_414 (coe v2)) in
                         coe
                           (let v7
                                  = coe
                                      du_exec'45'loop'45'run_2740 (coe v0) (coe v4)
                                      (coe
                                         du_loop'45'reanchor'45'loc_2728 (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe v0 v2 v3)))
                                      (coe
                                         du_loop'45'reanchor'45'alloc_2734 (coe v3)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe v0 v2 v3))) in
                            coe
                              (case coe v6 of
                                 C_SV'45'Tag_72 v8
                                   -> case coe v8 of
                                        0 -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                               (coe v3)
                                        _ -> coe v7
                                 _ -> coe v7)))))
-- Once.CCC.Machine.SMCore.AbstractExec.lit-value
d_lit'45'value_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> AgdaAny -> AgdaAny
d_lit'45'value_2800 v0 ~v1 v2 v3 = du_lit'45'value_2800 v0 v2 v3
du_lit'45'value_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> AgdaAny -> AgdaAny
du_lit'45'value_2800 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_fits'45'int_198 -> coe v2
      MAlonzo.Code.Once.Type.C_fits'45'float_200
        -> coe
             MAlonzo.Code.Once.Float.Dyadic.d_encode_140
             (coe
                MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_120
                (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2212 ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2806 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2214
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2216
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Output_58)))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe v3)
      C_load'45'indirect_2218
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1458 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1354
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2220
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1496 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1354
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2222 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2492
             (coe
                du_readLoc_638 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_572 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2224 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_804 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_572 (coe v3)) (coe v4))
                (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_store'45'indirect_2226
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1470 v0
                (coe
                   du_sv'45'as'45'loc_1354
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2228
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1508 v0
                (coe
                   du_sv'45'as'45'loc_1354
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_lea'45'slot_2230 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_572 (coe v3)) (coe v4))))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe v3)
      C_restore'45'input_2232 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2504
             (coe
                du_readLoc_638 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_572 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2234 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_584 (coe d_current'45'frame_572 (coe v3))
                (coe d_saved'45'frames_574 (coe v3))
                (coe d_frame'45'slots_576 (coe v3))
                (coe addInt (coe d_next'45'slot_578 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_580 (coe v3))
                (coe d_block'45'size_582 (coe v3)))
      C_instr'45'dealloc'45'stack_2236 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2238 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_584 (coe d_current'45'frame_572 (coe v3))
                (coe d_saved'45'frames_574 (coe v3))
                (coe d_frame'45'slots_576 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_580 (coe v3))
                (coe d_block'45'size_582 (coe v3)))
      C_instr'45'push'45'frame_2240 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2242
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2244
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2246 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2248 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_804 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_572 (coe v3)) (coe v4))
                (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_worklist'45'pop_2250 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2492
             (coe
                du_readLoc_638 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_572 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2252 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2258 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (d_exec'45'sigop'45'output_2690
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe du_exec'45'sigop'45'halts_2706 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2264 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Lit_76 (coe v4) (coe v5)
                      (coe du_lit'45'value_2800 (coe v0) (coe v5) (coe v6))))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2266 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Code_78 (coe v4)))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2268
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2270 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Tag_72 (coe v4)))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2272 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2812 (coe v0)
             (coe du_case'45'tag'45'at_2712 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2274 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422
                (coe
                   du_writeReg_160 (d_regs_414 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_580 (coe v3)))))))
                (coe d_stackMem_416 (coe v2)) (coe d_heapMem_418 (coe v2))
                (coe d_halted_420 (coe v2)))
             (coe
                C_mkAllocState_584 (coe d_current'45'frame_572 (coe v3))
                (coe d_saved'45'frames_574 (coe v3))
                (coe d_frame'45'slots_576 (coe v3))
                (coe d_next'45'slot_578 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_580 (coe v3)))))
                (coe
                   d_size'45'with_476 (coe v4)
                   (coe d_next'45'heap'45'ref_580 (coe v3))
                   (coe d_block'45'size_582 (coe v3))))
      C_instr'45'loop_2276 v4
        -> coe
             d_exec'45'loop_2810 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2278 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_442 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2280 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2282 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1484
                (coe
                   du_slot'45'base_1480
                   (coe
                      du_readLoc_638 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_572 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_396
                   (coe du_readReg_148 (coe d_regs_414 (coe v2)) (coe C_Scratch_60)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2212] ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2808 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_420 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2808 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2806 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2806 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2212] ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2810 v0 v1 v2 v3 v4
  = coe
      du_exec'45'loop'45'run_2740
      (coe d_exec'45'trace_2808 (coe v0) (coe v2)) (coe v1) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_2812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  [T_AbstractInstr_2212] ->
  [T_AbstractInstr_2212] ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2812 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_70 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_422 (coe d_regs_414 (coe v4))
                       (coe d_stackMem_416 (coe v4)) (coe d_heapMem_418 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Tag_72 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_2808 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2808 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_76 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_422 (coe d_regs_414 (coe v4))
                       (coe d_stackMem_416 (coe v4)) (coe d_heapMem_418 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Code_78 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_422 (coe d_regs_414 (coe v4))
                       (coe d_stackMem_416 (coe v4)) (coe d_heapMem_418 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_422 (coe d_regs_414 (coe v4))
                (coe d_stackMem_416 (coe v4)) (coe d_heapMem_418 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_3094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2212 ->
  [T_AbstractInstr_2212] ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3094 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2212 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3140 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2212 -> ()) -> [T_AbstractInstr_2212] -> ()
d_AllI_3174 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_488 -> AgdaAny) ->
  (T_AbstractInstr_2212 -> ()) ->
  (T_AbstractInstr_2212 ->
   T_LocState_402 ->
   T_AllocState_488 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2212] ->
  AgdaAny ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3202 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_488 -> AgdaAny) ->
  (T_AbstractInstr_2212 -> ()) ->
  (T_AbstractInstr_2212 ->
   T_LocState_402 ->
   T_AllocState_488 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2212] ->
  [T_AbstractInstr_2212] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3292 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_AllocState_488 -> Integer -> Maybe Integer
d_getTag_3424 ~v0 v1 v2 v3 = du_getTag_3424 v1 v2 v3
du_getTag_3424 ::
  T_LocState_402 -> T_AllocState_488 -> Integer -> Maybe Integer
du_getTag_3424 v0 v1 v2
  = let v3
          = coe d_stackMem_416 v0 (d_current'45'frame_572 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2286 ->
  T_LocState_402 ->
  T_AllocState_488 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3448 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2288
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2290 v4
        -> let v5 = d_halted_420 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2806 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2292 v4 v5
        -> let v6 = d_halted_420 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3448 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3448 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3448 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2294 v4 v5 v6
        -> let v7 = d_halted_420 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_416 v2 (d_current'45'frame_572 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3448 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3448 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3448 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3448 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3448 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2296 v4
        -> let v5 = d_halted_420 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3448 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2298 v4
        -> coe d_exec'45'trace_2808 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3608 ::
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3608 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2286 ->
  T_TreeTrace_2286 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3626 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2212 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3672 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2286 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3712 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2212] ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3752 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2212] ->
  [T_AbstractInstr_2212] ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3772 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3830
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2286 ->
  T_LocState_402 ->
  T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3838 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3838
du_exec'45'tree'45'flat'45'equiv'45'simple_3838 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3838
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
