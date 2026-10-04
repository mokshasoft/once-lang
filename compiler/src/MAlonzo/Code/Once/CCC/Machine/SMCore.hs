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
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Allocator.AbstractInstance
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word
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
    C_SV'45'Lit_76 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_FitsInReg_200 AgdaAny |
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
  = C_mkLocState_426 T_Registers_124
                     (AgdaAny -> Integer -> Maybe T_StoredValue_66)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_66)
                     Bool [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_416 :: T_LocState_402 -> T_Registers_124
d_regs_416 v0
  = case coe v0 of
      C_mkLocState_426 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_418 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_stackMem_418 v0
  = case coe v0 of
      C_mkLocState_426 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_420 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_heapMem_420 v0
  = case coe v0 of
      C_mkLocState_426 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_422 :: T_LocState_402 -> Bool
d_halted_422 v0
  = case coe v0 of
      C_mkLocState_426 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.ev-log
d_ev'45'log_424 ::
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_424 v0
  = case coe v0 of
      C_mkLocState_426 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_368 -> T_Registers_124 -> T_Registers_124
d_setReg_430 ~v0 v1 v2 = du_setReg_430 v1 v2
du_setReg_430 :: T_RegOp_368 -> T_Registers_124 -> T_Registers_124
du_setReg_430 v0 v1
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
d_exec'45'reg'45'op_446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_368 -> T_LocState_402 -> T_LocState_402
d_exec'45'reg'45'op_446 ~v0 v1 v2 = du_exec'45'reg'45'op_446 v1 v2
du_exec'45'reg'45'op_446 ::
  T_RegOp_368 -> T_LocState_402 -> T_LocState_402
du_exec'45'reg'45'op_446 v0 v1
  = coe
      C_mkLocState_426
      (coe du_setReg_430 (coe v0) (coe d_regs_416 (coe v1)))
      (coe d_stackMem_418 (coe v1)) (coe d_heapMem_420 (coe v1))
      (coe d_halted_422 (coe v1)) (coe d_ev'45'log_424 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_452 = ()
data T_AllocMode_452 = C_Stack_454 | C_Heap_456
-- Once.CCC.Machine.SMCore.size-with-aux
d_size'45'with'45'aux_464 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_size'45'with'45'aux_464 v0 v1 ~v2 v3 v4
  = du_size'45'with'45'aux_464 v0 v1 v3 v4
du_size'45'with'45'aux_464 ::
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_size'45'with'45'aux_464 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe v0)
             else coe seq (coe v5) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.size-with
d_size'45'with_480 ::
  Integer -> Integer -> (Integer -> Integer) -> Integer -> Integer
d_size'45'with_480 v0 v1 v2 v3
  = coe
      du_size'45'with'45'aux_464 (coe v0) (coe v3) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v1))
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_492 a0 = ()
data T_AllocState_492
  = C_mkAllocState_596 AgdaAny
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer Integer Integer
                       (Integer -> Integer)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_584 :: T_AllocState_492 -> AgdaAny
d_current'45'frame_584 v0
  = case coe v0 of
      C_mkAllocState_596 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_586 ::
  T_AllocState_492 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_586 v0
  = case coe v0 of
      C_mkAllocState_596 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.frame-slots
d_frame'45'slots_588 :: T_AllocState_492 -> Integer
d_frame'45'slots_588 v0
  = case coe v0 of
      C_mkAllocState_596 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_590 :: T_AllocState_492 -> Integer
d_next'45'slot_590 v0
  = case coe v0 of
      C_mkAllocState_596 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_592 :: T_AllocState_492 -> Integer
d_next'45'heap'45'ref_592 v0
  = case coe v0 of
      C_mkAllocState_596 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_594 :: T_AllocState_492 -> Integer -> Integer
d_block'45'size_594 v0
  = case coe v0 of
      C_mkAllocState_596 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_640 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_640 v0 v1 v2 = coe d_stackMem_418 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_648 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_648 v0 v1 = coe d_heapMem_420 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_654 ~v0 v1 v2 = du_readLoc_654 v1 v2
du_readLoc_654 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_654 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_418 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_420 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_674 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_674 v5 v6 v7 v8
du_writeStackMem'45'aux_674 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_674 v0 v1 v2 v3
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
d_writeStackMem_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_682 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_674
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_704 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_clear'45'frame'45'aux_704 v5 v6 v7
du_clear'45'frame'45'aux_704 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_704 v0 v1 v2
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
d_clear'45'frame_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_710 v0 v1 v2 v3 v4 v5
  = coe
      du_clear'45'frame'45'aux_704
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__90 v0 v2 v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v5)
         (coe v3))
      (coe v1 v4 v5)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-just
d_clear'45'frame'45'just_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_734 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_786 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_786 v3 v4 v5
du_writeHeapMem'45'aux_786 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_786 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_792 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_792 v1 v2 v3 v4
du_writeHeapMem_792 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_792 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_786
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_802 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_426 (coe d_regs_416 (coe v1))
      (coe
         d_writeStackMem_682 (coe v0) (coe d_stackMem_418 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_420 (coe v1)) (coe d_halted_422 (coe v1))
      (coe d_ev'45'log_424 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_812 ~v0 v1 v2 v3 = du_writeLocToHeap_812 v1 v2 v3
du_writeLocToHeap_812 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_812 v0 v1 v2
  = coe
      C_mkLocState_426 (coe d_regs_416 (coe v0))
      (coe d_stackMem_418 (coe v0))
      (coe
         du_writeHeapMem_792 (coe d_heapMem_420 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_422 (coe v0)) (coe d_ev'45'log_424 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_820 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_802 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_70 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_812 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_72 v5
               -> coe du_writeLocToHeap_812 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_76 v5 v6 v7
               -> coe du_writeLocToHeap_812 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_78 v5
               -> coe du_writeLocToHeap_812 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_870 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_908 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_948 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_948 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_968 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_968 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_996 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_996 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1028 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1028 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1306 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1358 a0 = ()
data T_LocSourceExt_1358
  = C_Loc_1362 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1364 T_AbstractReg_54 | C_IndRegSuc_1366 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1370 ~v0 v1 = du_sv'45'as'45'loc_1370 v1
du_sv'45'as'45'loc_1370 ::
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1370 v0
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
d_resolveSourceExt_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_LocSourceExt_1358 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1376 ~v0 v1 v2 = du_resolveSourceExt_1376 v1 v2
du_resolveSourceExt_1376 ::
  T_Registers_124 ->
  T_LocSourceExt_1358 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1376 v0 v1
  = case coe v1 of
      C_Loc_1362 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1364 v2
        -> coe
             du_sv'45'as'45'loc_1370 (coe du_readReg_148 (coe v0) (coe v2))
      C_IndRegSuc_1366 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1370 (coe du_readReg_148 (coe v0) (coe v2)) in
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
d_Instr_1406 a0 = ()
data T_Instr_1406
  = C_load_1410 T_AbstractReg_54 T_LocSourceExt_1358 |
    C_store_1412 T_LocSourceExt_1358 T_AbstractReg_54 |
    C_mov_1414 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_1422 v0 = coe d_clear'45'frame_710 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_1424 ~v0 = du_clear'45'frame'45'aux_1424
du_clear'45'frame'45'aux_1424 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_1424 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_704 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1426 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1428 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1428 v0 v1 = coe d_heapMem_420 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1430 ~v0 = du_readLoc_1430
du_readLoc_1430 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1430 = coe du_readLoc_654
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1432 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1432 v0 v1 v2 = coe d_stackMem_418 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1434 ~v0 = du_writeHeapMem_1434
du_writeHeapMem_1434 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1434 = coe du_writeHeapMem_792
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1436 ~v0 = du_writeHeapMem'45'aux_1436
du_writeHeapMem'45'aux_1436 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1436 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_786 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_1438 v0 = coe d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1440 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1442 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1442 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1444 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1446 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1446 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1448 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1450 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1452 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1452 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_1454 ~v0 = du_writeLocToHeap_1454
du_writeLocToHeap_1454 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_1454 = coe du_writeLocToHeap_812
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_1456 v0 = coe d_writeLocToStack_802 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1458 v0 = coe d_writeStackMem_682 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1460 ~v0 = du_writeStackMem'45'aux_1460
du_writeStackMem'45'aux_1460 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1460 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_674 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'load'45'with'45'value_1462 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1462 v1 v2
du_exec'45'load'45'with'45'value_1462 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
du_exec'45'load'45'with'45'value_1462 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_426 (coe du_writeReg_160 (d_regs_416 (coe v3)) v0 v2)
                  (coe d_stackMem_418 (coe v3)) (coe d_heapMem_420 (coe v3))
                  (coe d_halted_422 (coe v3)) (coe d_ev'45'log_424 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_426 (coe d_regs_416 (coe v2))
                  (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_424 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'via'45'resolved_1474 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1474 v1 v2
du_exec'45'load'45'via'45'resolved_1474 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'via'45'resolved_1474 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1462 v0
                  (coe du_readLoc_654 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_426 (coe d_regs_416 (coe v2))
                  (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_424 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'via'45'resolved_1486 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_820 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_426 (coe d_regs_416 (coe v3))
                  (coe d_stackMem_418 (coe v3)) (coe d_heapMem_420 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_424 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1496 ~v0 v1 = du_slot'45'base_1496 v1
du_slot'45'base_1496 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1496 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1370 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
d_exec'45'lea'45'indexed'45'via_1500 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1500 v1
du_exec'45'lea'45'indexed'45'via_1500 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
du_exec'45'lea'45'indexed'45'via_1500 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_426
                  (coe
                     du_writeReg_160 (d_regs_416 (coe v3)) (coe C_Input1_56)
                     (coe C_SV'45'Ptr_70 (coe du_offsetLoc_92 (coe v1) (coe v2))))
                  (coe d_stackMem_418 (coe v3)) (coe d_heapMem_420 (coe v3))
                  (coe d_halted_422 (coe v3)) (coe d_ev'45'log_424 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_426 (coe d_regs_416 (coe v2))
                  (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_424 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_1512 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1512 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1512 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_1512 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1462 v0
                  (coe du_readLoc_654 (coe v3) (coe du_sucLoc_82 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_426 (coe d_regs_416 (coe v2))
                  (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_424 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_1524 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_820
                  (coe v0) (coe v4) (coe du_sucLoc_82 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_426 (coe d_regs_416 (coe v3))
                  (coe d_stackMem_418 (coe v3)) (coe d_heapMem_420 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_424 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1406 -> T_LocState_402 -> T_LocState_402
d_exec_1534 v0 v1
  = case coe v1 of
      C_load_1410 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1474 v2
                  (coe du_resolveSourceExt_1376 (coe d_regs_416 (coe v4)) (coe v3))
                  v4)
      C_store_1412 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1486 v0
                  (coe du_resolveSourceExt_1376 (coe d_regs_416 (coe v4)) (coe v2))
                  (coe du_readReg_148 (coe d_regs_416 (coe v4)) (coe v3)) v4)
      C_mov_1414 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_426
                  (coe
                     du_writeReg_160 (d_regs_416 (coe v4)) v2
                     (coe du_readReg_148 (coe d_regs_416 (coe v4)) (coe v3)))
                  (coe d_stackMem_418 (coe v4)) (coe d_heapMem_420 (coe v4))
                  (coe d_halted_422 (coe v4)) (coe d_ev'45'log_424 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1560 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1566 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1406] -> T_LocState_402 -> T_LocState_402
d_execList_1568 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_422 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1568 (coe v0) (coe v4) (coe d_exec_1534 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_1600 v0 = coe d_clear'45'frame_710 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_1602 ~v0 = du_clear'45'frame'45'aux_1602
du_clear'45'frame'45'aux_1602 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_1602 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_704 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1604 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1606 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1606 v0 v1 = coe d_heapMem_420 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1608 ~v0 = du_readLoc_1608
du_readLoc_1608 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1608 = coe du_readLoc_654
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1610 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1610 v0 v1 v2 = coe d_stackMem_418 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1612 ~v0 = du_writeHeapMem_1612
du_writeHeapMem_1612 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1612 = coe du_writeHeapMem_792
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1614 ~v0 = du_writeHeapMem'45'aux_1614
du_writeHeapMem'45'aux_1614 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1614 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_786 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_1616 v0 = coe d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1618 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1620 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1620 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1622 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1624 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1624 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1626 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1628 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1630 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1630 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_1632 ~v0 = du_writeLocToHeap_1632
du_writeLocToHeap_1632 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_1632 = coe du_writeLocToHeap_812
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_1634 v0 = coe d_writeLocToStack_802 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1636 v0 = coe d_writeStackMem_682 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1638 ~v0 = du_writeStackMem'45'aux_1638
du_writeStackMem'45'aux_1638 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1638 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_674 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1406 -> T_LocState_402 -> T_LocState_402
d_exec_1642 v0 = coe d_exec_1534 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
d_exec'45'lea'45'indexed'45'via_1644 ~v0
  = du_exec'45'lea'45'indexed'45'via_1644
du_exec'45'lea'45'indexed'45'via_1644 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
du_exec'45'lea'45'indexed'45'via_1644
  = coe du_exec'45'lea'45'indexed'45'via_1500
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1646 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1648 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_1650 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1650
du_exec'45'load'45'suc'45'via'45'resolved_1650 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_1650
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1512
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'via'45'resolved_1652 ~v0
  = du_exec'45'load'45'via'45'resolved_1652
du_exec'45'load'45'via'45'resolved_1652 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'via'45'resolved_1652
  = coe du_exec'45'load'45'via'45'resolved_1474
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'load'45'with'45'value_1654 ~v0
  = du_exec'45'load'45'with'45'value_1654
du_exec'45'load'45'with'45'value_1654 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
du_exec'45'load'45'with'45'value_1654
  = coe du_exec'45'load'45'with'45'value_1462
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_1656 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1524 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'via'45'resolved_1658 v0
  = coe d_exec'45'store'45'via'45'resolved_1486 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1406] -> T_LocState_402 -> T_LocState_402
d_execList_1660 v0 = coe d_execList_1568 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1662 ~v0 = du_slot'45'base_1662
du_slot'45'base_1662 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1662 = coe du_slot'45'base_1496
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_LocSourceExt_1358 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_1664 ~v0 v1 v2
  = du_resolved'45'readLoc_1664 v1 v2
du_resolved'45'readLoc_1664 ::
  T_LocState_402 -> T_LocSourceExt_1358 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_1664 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1376 (coe d_regs_416 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_654 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1694 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1764 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1840 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1870 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1926 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1978 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2030 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2030 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2046 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2064 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2064 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2078 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2096 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2162 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2186 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2214 = ()
data T_FlatCtrl_2214
  = C_c'45'label_2216 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2218 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'scratch'45'zero_2220 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2222 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'entry_2224 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                      Integer |
    C_c'45'ret_2226 Integer |
    C_c'45'call'45'fn_2228 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 |
    C_c'45'start_2230 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2238 = ()
data T_AbstractInstr_2238
  = C_mov'45'to'45'output_2240 | C_mov'45'to'45'input_2242 |
    C_load'45'indirect_2244 | C_load'45'indirect'45'suc_2246 |
    C_load'45'from'45'slot_2248 Integer |
    C_store'45'at'45'slot_2250 Integer | C_store'45'indirect_2252 |
    C_store'45'indirect'45'suc_2254 | C_lea'45'slot_2256 Integer |
    C_restore'45'input_2258 Integer |
    C_instr'45'alloc'45'stack_2260 Integer |
    C_instr'45'dealloc'45'stack_2262 Integer |
    C_instr'45'reclaim'45'to_2264 Integer |
    C_instr'45'push'45'frame_2266 Integer |
    C_instr'45'pop'45'frame_2268 | C_instr'45'call'45'closure_2270 |
    C_worklist'45'init_2272 Integer | C_worklist'45'push_2274 Integer |
    C_worklist'45'pop_2276 Integer | C_worklist'45'check_2278 Integer |
    C_instr'45'sigop_2284 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 |
    C_instr'45'load'45'const_2290 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Type.T_FitsInReg_200 AgdaAny |
    C_instr'45'load'45'code'45'addr_2292 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2294 |
    C_instr'45'load'45'tag'45'lit_2296 Integer |
    C_instr'45'case'45'on'45'tag_2298 [T_AbstractInstr_2238]
                                      [T_AbstractInstr_2238] |
    C_instr'45'alloc'45'heap_2300 Integer |
    C_instr'45'loop_2302 [T_AbstractInstr_2238] |
    C_instr'45'reg'45'op_2304 T_RegOp_368 |
    C_instr'45'ctrl_2306 T_FlatCtrl_2214 |
    C_lea'45'indexed_2308 Integer
-- Once.CCC.Machine.SMCore.CallI
d_CallI_2310 :: T_AbstractInstr_2238 -> ()
d_CallI_2310 = erased
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2312 :: ()
d_AbstractTrace_2312 = erased
-- Once.CCC.Machine.SMCore.CompUnit
d_CompUnit_2314 = ()
data T_CompUnit_2314
  = C_unit_2328 Integer [T_AbstractInstr_2238]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Machine.SMCore.CompUnit.entry-budget
d_entry'45'budget_2322 :: T_CompUnit_2314 -> Integer
d_entry'45'budget_2322 v0
  = case coe v0 of
      C_unit_2328 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.entry
d_entry_2324 :: T_CompUnit_2314 -> [T_AbstractInstr_2238]
d_entry_2324 v0
  = case coe v0 of
      C_unit_2328 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.blocks
d_blocks_2326 ::
  T_CompUnit_2314 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2326 v0
  = case coe v0 of
      C_unit_2328 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.block-layout
d_block'45'layout_2330 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_AbstractInstr_2238]
d_block'45'layout_2330 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       C_instr'45'ctrl_2306
                       (coe
                          C_c'45'entry_2224
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_instr'45'ctrl_2306 (coe C_c'45'ret_2226 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout
d_blocks'45'layout_2338 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_AbstractInstr_2238]
d_blocks'45'layout_2338 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_block'45'layout_2330 (coe v1))
             (coe d_blocks'45'layout_2338 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout-++
d_blocks'45'layout'45''43''43'_2348 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blocks'45'layout'45''43''43'_2348 = erased
-- Once.CCC.Machine.SMCore.link
d_link_2360 :: T_CompUnit_2314 -> [T_AbstractInstr_2238]
d_link_2360 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2324 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2306
            (coe C_c'45'ret_2226 (coe d_entry'45'budget_2322 (coe v0))))
         (coe d_blocks'45'layout_2338 (coe d_blocks_2326 (coe v0))))
-- Once.CCC.Machine.SMCore.link-top
d_link'45'top_2364 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  T_CompUnit_2314 -> [T_AbstractInstr_2238]
d_link'45'top_2364 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2324 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe C_instr'45'ctrl_2306 (coe C_c'45'label_2216 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe C_instr'45'ctrl_2306 (coe C_c'45'jmp_2218 (coe v0)))
            (coe d_blocks'45'layout_2338 (coe d_blocks_2326 (coe v1)))))
-- Once.CCC.Machine.SMCore.link-pre
d_link'45'pre_2370 ::
  T_CompUnit_2314 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> [T_AbstractInstr_2238]
d_link'45'pre_2370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2324 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2306
            (coe C_c'45'ret_2226 (coe d_entry'45'budget_2322 (coe v0))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_blocks'45'layout_2338 (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  C_instr'45'ctrl_2306
                  (coe
                     C_c'45'entry_2224
                     (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2))
                     (coe v3)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Machine.SMCore.link-post
d_link'45'post_2380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [T_AbstractInstr_2238]
d_link'45'post_2380 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_instr'45'ctrl_2306 (coe C_c'45'ret_2226 (coe v1)))
      (coe d_blocks'45'layout_2338 (coe v0))
-- Once.CCC.Machine.SMCore.link-block-split
d_link'45'block'45'split_2398 ::
  T_CompUnit_2314 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_link'45'block'45'split_2398 = erased
-- Once.CCC.Machine.SMCore._.inner
d_inner_2418 ::
  T_CompUnit_2314 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_2418 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2426 = ()
data T_TreeTrace_2426
  = C_ε_2428 | C_instr_2430 T_AbstractInstr_2238 |
    C__'9656'__2432 T_TreeTrace_2426 T_TreeTrace_2426 |
    C_branch_2434 Integer T_TreeTrace_2426 T_TreeTrace_2426 |
    C_call'45'sub_2436 T_TreeTrace_2426 |
    C_flat_2438 [T_AbstractInstr_2238]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2440 :: [T_AbstractInstr_2238] -> T_TreeTrace_2426
d_flatToTree_2440 v0
  = case coe v0 of
      [] -> coe C_ε_2428
      (:) v1 v2
        -> coe
             C__'9656'__2432 (coe C_instr_2430 (coe v1))
             (coe d_flatToTree_2440 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2446 :: T_TreeTrace_2426 -> [T_AbstractInstr_2238]
d_treeToFlat_2446 v0
  = case coe v0 of
      C_ε_2428 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2430 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2432 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2446 (coe v1)) (coe d_treeToFlat_2446 (coe v2))
      C_branch_2434 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2446 (coe v2)) (coe d_treeToFlat_2446 (coe v3))
      C_call'45'sub_2436 v1 -> coe d_treeToFlat_2446 (coe v1)
      C_flat_2438 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2462 ::
  Integer -> T_TreeTrace_2426 -> [T_AbstractInstr_2238]
d_treeToRunnable_2462 v0 v1
  = case coe v1 of
      C_ε_2428 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2430 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2432 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2462 (coe v0) (coe v2))
             (coe d_treeToRunnable_2462 (coe v0) (coe v3))
      C_branch_2434 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2462 (coe v0) (coe v3))
             (coe d_treeToRunnable_2462 (coe v0) (coe v4))
      C_call'45'sub_2436 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2274 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2462 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2276 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2438 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2492 ::
  Integer -> T_TreeTrace_2426 -> [T_AbstractInstr_2238]
d_treeToRunnableWithInit_2492 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2272 (coe v0))
      (coe d_treeToRunnable_2462 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_2542 v0 = coe d_clear'45'frame_710 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_2544 ~v0 = du_clear'45'frame'45'aux_2544
du_clear'45'frame'45'aux_2544 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_2544 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_704 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2546 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2548 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_2548 v0 v1 = coe d_heapMem_420 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_2550 ~v0 = du_readLoc_2550
du_readLoc_2550 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_2550 = coe du_readLoc_654
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2552 ::
  T_LocState_402 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_2552 v0 v1 v2 = coe d_stackMem_418 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_2554 ~v0 = du_writeHeapMem_2554
du_writeHeapMem_2554 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_2554 = coe du_writeHeapMem_792
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_2556 ~v0 = du_writeHeapMem'45'aux_2556
du_writeHeapMem'45'aux_2556 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_2556 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_786 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLoc_2558 v0 = coe d_writeLoc_820 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2560 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2562 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2562 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2564 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2566 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2566 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2568 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2570 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2572 ::
  T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2572 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
d_writeLocToHeap_2574 ~v0 = du_writeLocToHeap_2574
du_writeLocToHeap_2574 ::
  T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_402
du_writeLocToHeap_2574 = coe du_writeLocToHeap_812
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_402
d_writeLocToStack_2576 v0 = coe d_writeLocToStack_802 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_2578 v0 = coe d_writeStackMem_682 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_2580 ~v0 = du_writeStackMem'45'aux_2580
du_writeStackMem'45'aux_2580 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_2580 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_674 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1406 -> T_LocState_402 -> T_LocState_402
d_exec_2584 v0 = coe d_exec_1534 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
d_exec'45'lea'45'indexed'45'via_2586 ~v0
  = du_exec'45'lea'45'indexed'45'via_2586
du_exec'45'lea'45'indexed'45'via_2586 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_402 -> T_LocState_402
du_exec'45'lea'45'indexed'45'via_2586
  = coe du_exec'45'lea'45'indexed'45'via_1500
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2588 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2590 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_2592 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2592
du_exec'45'load'45'suc'45'via'45'resolved_2592 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_2592
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1512
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
d_exec'45'load'45'via'45'resolved_2594 ~v0
  = du_exec'45'load'45'via'45'resolved_2594
du_exec'45'load'45'via'45'resolved_2594 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> T_LocState_402
du_exec'45'load'45'via'45'resolved_2594
  = coe du_exec'45'load'45'via'45'resolved_1474
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'load'45'with'45'value_2596 ~v0
  = du_exec'45'load'45'with'45'value_2596
du_exec'45'load'45'with'45'value_2596 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
du_exec'45'load'45'with'45'value_2596
  = coe du_exec'45'load'45'with'45'value_1462
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_2598 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1524 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_402 -> T_LocState_402
d_exec'45'store'45'via'45'resolved_2600 v0
  = coe d_exec'45'store'45'via'45'resolved_1486 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1406] -> T_LocState_402 -> T_LocState_402
d_execList_2602 v0 = coe d_execList_1568 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2604 ~v0 = du_slot'45'base_2604
du_slot'45'base_2604 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2604 = coe du_slot'45'base_1496
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2608 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  T_LocState_402 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2610 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2612 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2614 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2616 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2618 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2620 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1358 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2622 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2624 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2626 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2628 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_402 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2630 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2632 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_LocSourceExt_1358 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_2634 ~v0 = du_resolved'45'readLoc_2634
du_resolved'45'readLoc_2634 ::
  T_LocState_402 -> T_LocSourceExt_1358 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_2634 = coe du_resolved'45'readLoc_1664
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2636 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2636 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2636 ::
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2636 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe du_writeReg_160 (d_regs_416 (coe v1)) (coe C_Output_58) v3)
                (coe d_stackMem_418 (coe v1)) (coe d_heapMem_420 (coe v1))
                (coe d_halted_422 (coe v1)) (coe d_ev'45'log_424 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426 (coe d_regs_416 (coe v1))
                (coe d_stackMem_418 (coe v1)) (coe d_heapMem_420 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_424 (coe v1)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2648 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2648 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2648 ::
  Maybe T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2648 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe du_writeReg_160 (d_regs_416 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_418 (coe v1)) (coe d_heapMem_420 (coe v1))
                (coe d_halted_422 (coe v1)) (coe d_ev'45'log_424 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426 (coe d_regs_416 (coe v1))
                (coe d_stackMem_418 (coe v1)) (coe d_heapMem_420 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_424 (coe v1)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2666 ::
  T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2666 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2672 ::
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2672 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2680 ::
  T_StoredValue_66 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2680 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2686 ::
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2686 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66
d_unit'45'storedvalue_2688 ~v0 = du_unit'45'storedvalue_2688
du_unit'45'storedvalue_2688 :: T_StoredValue_66
du_unit'45'storedvalue_2688
  = coe
      C_SV'45'Lit_76 (coe MAlonzo.Code.Once.Type.C_Int_134)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_202) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2694 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2694 v3 v4
du_combine'45'typed_2694 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2694 v0 v1
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
d_readTyped'45'int_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 -> Maybe Integer
d_readTyped'45'int_2700 ~v0 v1 = du_readTyped'45'int_2700 v1
du_readTyped'45'int_2700 :: Maybe T_StoredValue_66 -> Maybe Integer
du_readTyped'45'int_2700 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_202
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-float
d_readTyped'45'float_2704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 -> Maybe Integer
d_readTyped'45'float_2704 ~v0 v1 = du_readTyped'45'float_2704 v1
du_readTyped'45'float_2704 ::
  Maybe T_StoredValue_66 -> Maybe Integer
du_readTyped'45'float_2704 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_204
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-cell
d_readTyped'45'cell_2710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 -> Maybe AgdaAny
d_readTyped'45'cell_2710 ~v0 ~v1 v2 v3 v4
  = du_readTyped'45'cell_2710 v2 v3 v4
du_readTyped'45'cell_2710 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 -> Maybe AgdaAny
du_readTyped'45'cell_2710 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             C_SV'45'Ptr_70 v4 -> coe v0 v4
             C_SV'45'Tag_72 v4 -> coe v1 v3
             C_SV'45'Lit_76 v4 v5 v6 -> coe v1 v3
             C_SV'45'Code_78 v4 -> coe v1 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-pair
d_readTyped'45'pair_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_2746 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_readTyped'45'pair_2746 v3 v4 v5 v6 v7 v8
du_readTyped'45'pair_2746 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2746 v0 v1 v2 v3 v4 v5
  = coe
      du_combine'45'typed_2694
      (coe du_readTyped'45'cell_2710 (coe v0) (coe v2) (coe v4))
      (coe du_readTyped'45'cell_2710 (coe v1) (coe v3) (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_StoredValue_66 -> Maybe AgdaAny
d_readReg'45'typed_2762 ~v0 v1 v2 = du_readReg'45'typed_2762 v1 v2
du_readReg'45'typed_2762 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_StoredValue_66 -> Maybe AgdaAny
du_readReg'45'typed_2762 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_120
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C_Int_134
           -> case coe v1 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_202
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Float_136
           -> case coe v1 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_204
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-sum
d_readTyped'45'sum_2772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_2772 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'sum_2772 v3 v4 v5 v6
du_readTyped'45'sum_2772 ::
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_2772 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             C_SV'45'Ptr_70 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Tag_72 v5
               -> case coe v5 of
                    0 -> coe
                           MAlonzo.Code.Data.Maybe.Base.du_map_64
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38) (coe v0 v3)
                    1 -> coe
                           MAlonzo.Code.Data.Maybe.Base.du_map_64
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42) (coe v1 v3)
                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Lit_76 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Code_78 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped
d_readTyped_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> Maybe AgdaAny
d_readTyped_2818 ~v0 v1 v2 v3 = du_readTyped_2818 v1 v2 v3
du_readTyped_2818 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_402 -> Maybe AgdaAny
du_readTyped_2818 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_120
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C__'42'__124 v4 v5
           -> coe
                du_readTyped'45'pair_2746
                (coe (\ v6 -> coe du_readTyped_2818 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2818 (coe v5) (coe v6) (coe v2)))
                (coe du_readReg'45'typed_2762 (coe v4))
                (coe du_readReg'45'typed_2762 (coe v5))
                (coe du_readLoc_654 (coe v2) (coe v1))
                (coe du_readLoc_654 (coe v2) (coe du_sucLoc_82 (coe v1)))
         MAlonzo.Code.Once.Type.C__'43'__126 v4 v5
           -> coe
                du_readTyped'45'sum_2772
                (coe
                   du_readTyped'45'cell_2710
                   (coe (\ v6 -> coe du_readTyped_2818 (coe v4) (coe v6) (coe v2)))
                   (coe du_readReg'45'typed_2762 (coe v4)))
                (coe
                   du_readTyped'45'cell_2710
                   (coe (\ v6 -> coe du_readTyped_2818 (coe v5) (coe v6) (coe v2)))
                   (coe du_readReg'45'typed_2762 (coe v5)))
                (coe du_readLoc_654 (coe v2) (coe v1))
                (coe du_readLoc_654 (coe v2) (coe du_sucLoc_82 (coe v1)))
         MAlonzo.Code.Once.Type.C_Int_134
           -> coe
                du_readTyped'45'int_2700 (coe du_readLoc_654 (coe v2) (coe v1))
         MAlonzo.Code.Once.Type.C_Float_136
           -> coe
                du_readTyped'45'float_2704 (coe du_readLoc_654 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2864
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.decode-at
d_decode'45'at_2868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  T_StoredValue_66 -> T_LocState_402 -> Maybe AgdaAny
d_decode'45'at_2868 ~v0 v1 v2 v3 v4
  = du_decode'45'at_2868 v1 v2 v3 v4
du_decode'45'at_2868 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  T_StoredValue_66 -> T_LocState_402 -> Maybe AgdaAny
du_decode'45'at_2868 v0 v1 v2 v3
  = let v4
          = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v2 of
                 C_SV'45'Ptr_70 v5
                   -> coe du_readTyped_2818 (coe v0) (coe v5) (coe v3)
                 _ -> coe v4) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202
           -> case coe v2 of
                C_SV'45'Lit_76 v5 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_202
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204
           -> case coe v2 of
                C_SV'45'Lit_76 v5 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_204
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.events-at-arg
d_events'45'at'45'arg_2884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_events'45'at'45'arg_2884 ~v0 v1 ~v2 v3 v4
  = du_events'45'at'45'arg_2884 v1 v3 v4
du_events'45'at'45'arg_2884 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_events'45'at'45'arg_2884 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Denotation.Trace.C_mk'45'event_142
                (MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v1)) v0 v3)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.machine-events
d_machine'45'events_2898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_machine'45'events_2898 ~v0 v1 ~v2 v3 v4
  = du_machine'45'events_2898 v1 v3 v4
du_machine'45'events_2898 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_machine'45'events_2898 v0 v1 v2
  = coe
      du_events'45'at'45'arg_2884 (coe v0) (coe v1)
      (coe
         du_decode'45'at_2868 (coe v0)
         (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v1))
         (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Input1_56))
         (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_2910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> T_StoredValue_66
d_call'45'sigop'45'ans'45'at_2910 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             C_SV'45'Lit_76 (coe v2) (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.d_answer_482
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0))
                (d_ev'45'log_424 (coe v4))
                (coe
                   MAlonzo.Code.Once.Denotation.TraceMonad.C_callOp_142
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v3)) (coe v1)
                   (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3)) (coe v2))
                v6 v8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2688
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans
d_call'45'sigop'45'ans_2940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_StoredValue_66
d_call'45'sigop'45'ans_2940 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           d_call'45'sigop'45'ans'45'at_2910 (coe v0) (coe v1) (coe v2)
                           (coe v3) (coe v4) (coe v5) (coe v9)
                           (coe
                              du_decode'45'at_2868 (coe v1)
                              (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3))
                              (coe du_readReg_148 (coe d_regs_416 (coe v4)) (coe C_Input1_56))
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v8) (coe du_unit'45'storedvalue_2688)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-dec
d_call'45'sigop'45'dec_2962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_2962 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Contract.d__'8712'K'63'__176
      (MAlonzo.Code.Once.Denotation.TraceMonad.d_callKey_454
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.C_callOp_142
            (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v3)) (coe v1)
            (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3)) (coe v2)))
      (MAlonzo.Code.Once.Denotation.TraceMonad.d_calls_470
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_128 (coe v0)))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-val
d_call'45'sigop'45'val_2974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 -> T_StoredValue_66
d_call'45'sigop'45'val_2974 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_call'45'sigop'45'ans_2940 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe
                d_call'45'sigop'45'dec_2962 (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2688
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_2990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 -> T_StoredValue_66
d_call'45'sigop'45'output_2990 v0 v1 v2 v3 v4
  = coe
      d_call'45'sigop'45'val_2974 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_3002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 -> T_StoredValue_66
d_pure'45'sigop'45'output_3002 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_3032 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_208 (coe v2))
      (coe
         du_sv'45'as'45'loc_1370
         (coe du_readReg_148 (coe d_regs_416 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_3008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe AgdaAny -> T_StoredValue_66
d_pure'45'sigop'45'out'45'val_3008 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_res'45'sv_3012 (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_342 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_162 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_166
                   (coe v0))
                v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2688
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.res-sv
d_res'45'sv_3012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_66
d_res'45'sv_3012 ~v0 v1 v2 v3 = du_res'45'sv_3012 v1 v2 v3
du_res'45'sv_3012 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_66
du_res'45'sv_3012 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe du_unit'45'storedvalue_2688
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe C_SV'45'Lit_76 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_3032 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_200 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_3032 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    d_pure'45'sigop'45'out'45'val_3008 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe du_readTyped_2818 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    d_pure'45'sigop'45'out'45'val_3008 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2762 (coe v1)
                       (coe du_readReg_148 (coe d_regs_416 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2864 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3068 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 -> T_StoredValue_66
d_exec'45'sigop'45'output'45'of_3068 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe
             d_pure'45'sigop'45'output_3002 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe du_unit'45'storedvalue_2688
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe du_unit'45'storedvalue_2688
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe
             d_call'45'sigop'45'output_2990 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_3082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events'45'of_3082 ~v0 v1 ~v2 v3 v4 v5
  = du_sigop'45'events'45'of_3082 v1 v3 v4 v5
du_sigop'45'events'45'of_3082 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events'45'of_3082 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe du_machine'45'events_2898 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe du_machine'45'events_2898 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe du_machine'45'events_2898 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events
d_sigop'45'events_3100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events_3100 ~v0 v1 ~v2 v3 v4
  = du_sigop'45'events_3100 v1 v3 v4
du_sigop'45'events_3100 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events_3100 v0 v1 v2
  = coe
      du_sigop'45'events'45'of_3082 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_3110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 -> T_StoredValue_66
d_exec'45'sigop'45'output_3110 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_3068 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 -> Bool
d_exec'45'sigop'45'halts'45'of_3120 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_3120 v3
du_exec'45'sigop'45'halts'45'of_3120 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 -> Bool
du_exec'45'sigop'45'halts'45'of_3120 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Halts_134
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_3126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_402 -> Bool
d_exec'45'sigop'45'halts_3126 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_3126 v3
du_exec'45'sigop'45'halts_3126 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> Bool
du_exec'45'sigop'45'halts_3126 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_3120
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_352 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-fuel
d_loop'45'fuel_3132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_loop'45'fuel_3132 ~v0 = du_loop'45'fuel_3132
du_loop'45'fuel_3132 :: Integer
du_loop'45'fuel_3132 = coe (1000000 :: Integer)
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_3134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> Maybe T_StoredValue_66
d_case'45'tag'45'at_3134 ~v0 v1 = du_case'45'tag'45'at_3134 v1
du_case'45'tag'45'at_3134 ::
  T_LocState_402 -> Maybe T_StoredValue_66
du_case'45'tag'45'at_3134 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1370
              (coe d_input1_136 (coe d_regs_416 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_654 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.BodyRunner
d_BodyRunner_3148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_3148 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_3150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_LocState_402 -> T_LocState_402
d_loop'45'reanchor'45'loc_3150 ~v0 v1 v2
  = du_loop'45'reanchor'45'loc_3150 v1 v2
du_loop'45'reanchor'45'loc_3150 ::
  T_LocState_402 -> T_LocState_402 -> T_LocState_402
du_loop'45'reanchor'45'loc_3150 v0 v1
  = coe
      C_mkLocState_426 (coe d_regs_416 (coe v1))
      (coe d_stackMem_418 (coe v0)) (coe d_heapMem_420 (coe v1))
      (coe d_halted_422 (coe v1)) (coe d_ev'45'log_424 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_3156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_492 -> T_AllocState_492 -> T_AllocState_492
d_loop'45'reanchor'45'alloc_3156 ~v0 v1 v2
  = du_loop'45'reanchor'45'alloc_3156 v1 v2
du_loop'45'reanchor'45'alloc_3156 ::
  T_AllocState_492 -> T_AllocState_492 -> T_AllocState_492
du_loop'45'reanchor'45'alloc_3156 v0 v1
  = coe
      C_mkAllocState_596 (coe d_current'45'frame_584 (coe v0))
      (coe d_saved'45'frames_586 (coe v1))
      (coe d_frame'45'slots_588 (coe v1))
      (coe d_next'45'slot_590 (coe v0))
      (coe d_next'45'heap'45'ref_592 (coe v1))
      (coe d_block'45'size_594 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_3162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_402 ->
   T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_3162 ~v0 v1 v2 v3 v4
  = du_exec'45'loop'45'run_3162 v1 v2 v3 v4
du_exec'45'loop'45'run_3162 ::
  (T_LocState_402 ->
   T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_3162 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426 (coe d_regs_416 (coe v2))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_422 (coe v2) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                   else (let v6 = d_scratch_140 (coe d_regs_416 (coe v2)) in
                         coe
                           (let v7
                                  = coe
                                      du_exec'45'loop'45'run_3162 (coe v0) (coe v4)
                                      (coe
                                         du_loop'45'reanchor'45'loc_3150 (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe v0 v2 v3)))
                                      (coe
                                         du_loop'45'reanchor'45'alloc_3156 (coe v3)
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
d_lit'45'value_3222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny -> AgdaAny
d_lit'45'value_3222 v0 ~v1 v2 v3 = du_lit'45'value_3222 v0 v2 v3
du_lit'45'value_3222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_200 -> AgdaAny -> AgdaAny
du_lit'45'value_3222 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_fits'45'int_202
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20
             (coe
                mulInt (coe (8 :: Integer))
                (coe
                   MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_110 (coe v0)))
             (coe v2)
      MAlonzo.Code.Once.Type.C_fits'45'float_204
        -> coe
             MAlonzo.Code.Once.Float.Decimal.d_round_174
             (coe
                MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_126
                (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_3228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_3228 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2240
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2242
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Output_58)))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      C_load'45'indirect_2244
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1474 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1370
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2246
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1512 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1370
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2248 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2636
             (coe
                du_readLoc_654 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_584 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2250 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_820 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_584 (coe v3)) (coe v4))
                (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_store'45'indirect_2252
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1486 v0
                (coe
                   du_sv'45'as'45'loc_1370
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2254
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1524 v0
                (coe
                   du_sv'45'as'45'loc_1370
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_lea'45'slot_2256 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_584 (coe v3)) (coe v4))))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      C_restore'45'input_2258 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2648
             (coe
                du_readLoc_654 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_584 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2260 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'dealloc'45'stack_2262 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2264 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'push'45'frame_2266 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2268
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2270
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2272 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2274 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_820 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_584 (coe v3)) (coe v4))
                (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_worklist'45'pop_2276 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2636
             (coe
                du_readLoc_654 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_584 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2278 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2284 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (d_exec'45'sigop'45'output_3110
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe du_exec'45'sigop'45'halts_3126 (coe v6))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_ev'45'log_424 (coe v2))
                   (coe du_sigop'45'events_3100 (coe v4) (coe v6) (coe v2))))
             (coe v3)
      C_instr'45'load'45'const_2290 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Lit_76 (coe v4) (coe v5)
                      (coe du_lit'45'value_3222 (coe v0) (coe v5) (coe v6))))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2292 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Code_78 (coe v4)))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2294
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2296 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Tag_72 (coe v4)))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2298 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_3234 (coe v0)
             (coe du_case'45'tag'45'at_3134 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2300 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426
                (coe
                   du_writeReg_160 (d_regs_416 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_592 (coe v3)))))))
                (coe d_stackMem_418 (coe v2)) (coe d_heapMem_420 (coe v2))
                (coe d_halted_422 (coe v2)) (coe d_ev'45'log_424 (coe v2)))
             (coe
                C_mkAllocState_596 (coe d_current'45'frame_584 (coe v3))
                (coe d_saved'45'frames_586 (coe v3))
                (coe d_frame'45'slots_588 (coe v3))
                (coe d_next'45'slot_590 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_592 (coe v3)))))
                (coe
                   d_size'45'with_480 (coe v4)
                   (coe d_next'45'heap'45'ref_592 (coe v3))
                   (coe d_block'45'size_594 (coe v3))))
      C_instr'45'loop_2302 v4
        -> coe
             d_exec'45'loop_3232 (coe v0) (coe du_loop'45'fuel_3132) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2304 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_446 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2306 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2308 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1500
                (coe
                   du_slot'45'base_1496
                   (coe
                      du_readLoc_654 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_584 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_396
                   (coe du_readReg_148 (coe d_regs_416 (coe v2)) (coe C_Scratch_60)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_3230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2238] ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_3230 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_422 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_3230 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_3228 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_3228 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_3232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2238] ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_3232 v0 v1 v2 v3 v4
  = coe
      du_exec'45'loop'45'run_3162
      (coe d_exec'45'trace_3230 (coe v0) (coe v2)) (coe v1) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_3234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  [T_AbstractInstr_2238] ->
  [T_AbstractInstr_2238] ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_3234 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_70 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_426 (coe d_regs_416 (coe v4))
                       (coe d_stackMem_418 (coe v4)) (coe d_heapMem_420 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe d_ev'45'log_424 (coe v4)))
                    (coe v5)
             C_SV'45'Tag_72 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_3230 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_3230 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_76 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_426 (coe d_regs_416 (coe v4))
                       (coe d_stackMem_418 (coe v4)) (coe d_heapMem_420 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe d_ev'45'log_424 (coe v4)))
                    (coe v5)
             C_SV'45'Code_78 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_426 (coe d_regs_416 (coe v4))
                       (coe d_stackMem_418 (coe v4)) (coe d_heapMem_420 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe d_ev'45'log_424 (coe v4)))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_426 (coe d_regs_416 (coe v4))
                (coe d_stackMem_418 (coe v4)) (coe d_heapMem_420 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_424 (coe v4)))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_3516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  [T_AbstractInstr_2238] ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3516 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3562 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2238 -> ()) -> [T_AbstractInstr_2238] -> ()
d_AllI_3596 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_492 -> AgdaAny) ->
  (T_AbstractInstr_2238 -> ()) ->
  (T_AbstractInstr_2238 ->
   T_LocState_402 ->
   T_AllocState_492 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2238] ->
  AgdaAny ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3624 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_492 -> AgdaAny) ->
  (T_AbstractInstr_2238 -> ()) ->
  (T_AbstractInstr_2238 ->
   T_LocState_402 ->
   T_AllocState_492 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2238] ->
  [T_AbstractInstr_2238] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3714 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_402 -> T_AllocState_492 -> Integer -> Maybe Integer
d_getTag_3846 ~v0 v1 v2 v3 = du_getTag_3846 v1 v2 v3
du_getTag_3846 ::
  T_LocState_402 -> T_AllocState_492 -> Integer -> Maybe Integer
du_getTag_3846 v0 v1 v2
  = let v3
          = coe d_stackMem_418 v0 (d_current'45'frame_584 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2426 ->
  T_LocState_402 ->
  T_AllocState_492 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3870 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2428
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2430 v4
        -> let v5 = d_halted_422 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_3228 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2432 v4 v5
        -> let v6 = d_halted_422 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3870 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3870 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3870 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2434 v4 v5 v6
        -> let v7 = d_halted_422 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_418 v2 (d_current'45'frame_584 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3870 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3870 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3870 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3870 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3870 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2436 v4
        -> let v5 = d_halted_422 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3870 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2438 v4
        -> coe d_exec'45'trace_3230 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_4030 ::
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_4030 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_4048 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2426 ->
  T_TreeTrace_2426 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_4048 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_4094 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_4094 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_4134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2426 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_4134 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_4174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2238] ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_4174 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_4194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2238] ->
  [T_AbstractInstr_2238] ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_4194 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_4252
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_4260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2426 ->
  T_LocState_402 ->
  T_AllocState_492 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_4260 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_4260
du_exec'45'tree'45'flat'45'equiv'45'simple_4260 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_4260
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
