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
  = C_Input1_56 | C_Input2_58 | C_Output_60 | C_Scratch_62 |
    C_Count_64
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_68 a0 = ()
data T_StoredValue_68
  = C_SV'45'Ptr_72 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_SV'45'Tag_74 Integer |
    C_SV'45'Lit_78 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_SV'45'Code_80 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sucLoc_84 ~v0 v1 = du_sucLoc_84 v1
du_sucLoc_84 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sucLoc_84 v0
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
d_offsetLoc_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_offsetLoc_94 ~v0 v1 v2 = du_offsetLoc_94 v1 v2
du_offsetLoc_94 ::
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_offsetLoc_94 v0 v1
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
d_StackMem_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_108 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_HeapMem_114 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__122 ::
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__122 v0 v1
  = case coe v0 of
      C_Input1_56
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Input2_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Input2_58
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_60
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Scratch_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Scratch_62
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Count_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Count_64
        -> case coe v1 of
             C_Input1_56
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Count_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_126 a0 = ()
data T_Registers_126
  = C_mkRegs_150 T_StoredValue_68 T_StoredValue_68 T_StoredValue_68
                 T_StoredValue_68 T_StoredValue_68
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_140 :: T_Registers_126 -> T_StoredValue_68
d_input1_140 v0
  = case coe v0 of
      C_mkRegs_150 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_142 :: T_Registers_126 -> T_StoredValue_68
d_input2_142 v0
  = case coe v0 of
      C_mkRegs_150 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_144 :: T_Registers_126 -> T_StoredValue_68
d_output_144 v0
  = case coe v0 of
      C_mkRegs_150 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.scratch
d_scratch_146 :: T_Registers_126 -> T_StoredValue_68
d_scratch_146 v0
  = case coe v0 of
      C_mkRegs_150 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.count
d_count_148 :: T_Registers_126 -> T_StoredValue_68
d_count_148 v0
  = case coe v0 of
      C_mkRegs_150 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 -> T_AbstractReg_54 -> T_StoredValue_68
d_readReg_154 ~v0 v1 v2 = du_readReg_154 v1 v2
du_readReg_154 ::
  T_Registers_126 -> T_AbstractReg_54 -> T_StoredValue_68
du_readReg_154 v0 v1
  = case coe v1 of
      C_Input1_56 -> coe d_input1_140 (coe v0)
      C_Input2_58 -> coe d_input2_142 (coe v0)
      C_Output_60 -> coe d_output_144 (coe v0)
      C_Scratch_62 -> coe d_scratch_146 (coe v0)
      C_Count_64 -> coe d_count_148 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 -> T_StoredValue_68 -> T_Registers_126
d_writeReg_168 ~v0 v1 v2 = du_writeReg_168 v1 v2
du_writeReg_168 ::
  T_Registers_126 ->
  T_AbstractReg_54 -> T_StoredValue_68 -> T_Registers_126
du_writeReg_168 v0 v1
  = case coe v1 of
      C_Input1_56
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_150 (coe v2) (coe d_input2_142 (coe v0))
                  (coe d_output_144 (coe v0)) (coe d_scratch_146 (coe v0))
                  (coe d_count_148 (coe v0)))
      C_Input2_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_150 (coe d_input1_140 (coe v0)) (coe v2)
                  (coe d_output_144 (coe v0)) (coe d_scratch_146 (coe v0))
                  (coe d_count_148 (coe v0)))
      C_Output_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_150 (coe d_input1_140 (coe v0))
                  (coe d_input2_142 (coe v0)) (coe v2) (coe d_scratch_146 (coe v0))
                  (coe d_count_148 (coe v0)))
      C_Scratch_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_150 (coe d_input1_140 (coe v0))
                  (coe d_input2_142 (coe v0)) (coe d_output_144 (coe v0)) (coe v2)
                  (coe d_count_148 (coe v0)))
      C_Count_64
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_150 (coe d_input1_140 (coe v0))
                  (coe d_input2_142 (coe v0)) (coe d_output_144 (coe v0))
                  (coe d_scratch_146 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_204 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_384 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_416 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_448 = ()
data T_RegOp_448
  = C_scratch'45'one_450 | C_scratch'45'zero_452 |
    C_scratch'45'dec_454 | C_scratch'45'load'45'count_456 |
    C_count'45'zero_458 | C_count'45'inc_460
-- Once.CCC.Machine.SMCore.sv-succ
d_sv'45'succ_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 -> T_StoredValue_68
d_sv'45'succ_464 ~v0 v1 = du_sv'45'succ_464 v1
du_sv'45'succ_464 :: T_StoredValue_68 -> T_StoredValue_68
du_sv'45'succ_464 v0
  = let v1 = coe C_SV'45'Tag_74 (coe (1 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_74 v2
           -> coe C_SV'45'Tag_74 (coe addInt (coe (1 :: Integer)) (coe v2))
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-pred
d_sv'45'pred_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 -> T_StoredValue_68
d_sv'45'pred_470 ~v0 v1 = du_sv'45'pred_470 v1
du_sv'45'pred_470 :: T_StoredValue_68 -> T_StoredValue_68
du_sv'45'pred_470 v0
  = let v1 = coe C_SV'45'Tag_74 (coe (0 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_74 v2
           -> case coe v2 of
                _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                    let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                    coe (coe C_SV'45'Tag_74 (coe v3))
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-tag-val
d_sv'45'tag'45'val_476 :: T_StoredValue_68 -> Integer
d_sv'45'tag'45'val_476 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_SV'45'Tag_74 v2 -> coe v2
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.LocState
d_LocState_482 a0 = ()
data T_LocState_482
  = C_mkLocState_502 T_Registers_126
                     (AgdaAny -> Integer -> Maybe T_StoredValue_68)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_68)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_494 :: T_LocState_482 -> T_Registers_126
d_regs_494 v0
  = case coe v0 of
      C_mkLocState_502 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_496 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_stackMem_496 v0
  = case coe v0 of
      C_mkLocState_502 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_498 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_heapMem_498 v0
  = case coe v0 of
      C_mkLocState_502 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_500 :: T_LocState_482 -> Bool
d_halted_500 v0
  = case coe v0 of
      C_mkLocState_502 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_448 -> T_Registers_126 -> T_Registers_126
d_setReg_506 ~v0 v1 v2 = du_setReg_506 v1 v2
du_setReg_506 :: T_RegOp_448 -> T_Registers_126 -> T_Registers_126
du_setReg_506 v0 v1
  = case coe v0 of
      C_scratch'45'one_450
        -> coe
             du_writeReg_168 v1 (coe C_Scratch_62)
             (coe C_SV'45'Tag_74 (coe (1 :: Integer)))
      C_scratch'45'zero_452
        -> coe
             du_writeReg_168 v1 (coe C_Scratch_62)
             (coe C_SV'45'Tag_74 (coe (0 :: Integer)))
      C_scratch'45'dec_454
        -> coe
             du_writeReg_168 v1 (coe C_Scratch_62)
             (coe
                du_sv'45'pred_470 (coe du_readReg_154 (coe v1) (coe C_Scratch_62)))
      C_scratch'45'load'45'count_456
        -> coe
             du_writeReg_168 v1 (coe C_Scratch_62)
             (coe du_readReg_154 (coe v1) (coe C_Count_64))
      C_count'45'zero_458
        -> coe
             du_writeReg_168 v1 (coe C_Count_64)
             (coe C_SV'45'Tag_74 (coe (0 :: Integer)))
      C_count'45'inc_460
        -> coe
             du_writeReg_168 v1 (coe C_Count_64)
             (coe
                du_sv'45'succ_464 (coe du_readReg_154 (coe v1) (coe C_Count_64)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_448 -> T_LocState_482 -> T_LocState_482
d_exec'45'reg'45'op_522 ~v0 v1 v2 = du_exec'45'reg'45'op_522 v1 v2
du_exec'45'reg'45'op_522 ::
  T_RegOp_448 -> T_LocState_482 -> T_LocState_482
du_exec'45'reg'45'op_522 v0 v1
  = coe
      C_mkLocState_502
      (coe du_setReg_506 (coe v0) (coe d_regs_494 (coe v1)))
      (coe d_stackMem_496 (coe v1)) (coe d_heapMem_498 (coe v1))
      (coe d_halted_500 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_528 = ()
data T_AllocMode_528 = C_Stack_530 | C_Heap_532
-- Once.CCC.Machine.SMCore.size-with-aux
d_size'45'with'45'aux_540 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_size'45'with'45'aux_540 v0 v1 ~v2 v3 v4
  = du_size'45'with'45'aux_540 v0 v1 v3 v4
du_size'45'with'45'aux_540 ::
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_size'45'with'45'aux_540 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe v0)
             else coe seq (coe v5) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.size-with
d_size'45'with_556 ::
  Integer -> Integer -> (Integer -> Integer) -> Integer -> Integer
d_size'45'with_556 v0 v1 v2 v3
  = coe
      du_size'45'with'45'aux_540 (coe v0) (coe v3) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v1))
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_568 a0 = ()
data T_AllocState_568
  = C_mkAllocState_660 AgdaAny
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer Integer Integer
                       (Integer -> Integer)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_648 :: T_AllocState_568 -> AgdaAny
d_current'45'frame_648 v0
  = case coe v0 of
      C_mkAllocState_660 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_650 ::
  T_AllocState_568 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_650 v0
  = case coe v0 of
      C_mkAllocState_660 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.frame-slots
d_frame'45'slots_652 :: T_AllocState_568 -> Integer
d_frame'45'slots_652 v0
  = case coe v0 of
      C_mkAllocState_660 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_654 :: T_AllocState_568 -> Integer
d_next'45'slot_654 v0
  = case coe v0 of
      C_mkAllocState_660 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_656 :: T_AllocState_568 -> Integer
d_next'45'heap'45'ref_656 v0
  = case coe v0 of
      C_mkAllocState_660 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_658 :: T_AllocState_568 -> Integer -> Integer
d_block'45'size_658 v0
  = case coe v0 of
      C_mkAllocState_660 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_698 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_698 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_706 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_706 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_712 ~v0 v1 v2 = du_readLoc_712 v1 v2
du_readLoc_712 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_712 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_496 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_498 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_732 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_732 v5 v6 v7 v8
du_writeStackMem'45'aux_732 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_732 v0 v1 v2 v3
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
d_writeStackMem_740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_740 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_732
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
d_clear'45'frame'45'aux_762 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_clear'45'frame'45'aux_762 v5 v6 v7
du_clear'45'frame'45'aux_762 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
du_clear'45'frame'45'aux_762 v0 v1 v2
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
d_clear'45'frame_768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_clear'45'frame_768 v0 v1 v2 v3 v4 v5
  = coe
      du_clear'45'frame'45'aux_762
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v2 v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v5)
         (coe v3))
      (coe v1 v4 v5)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-just
d_clear'45'frame'45'just_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_792 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_844 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_844 v3 v4 v5
du_writeHeapMem'45'aux_844 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_844 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_850 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_850 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_850 v1 v2 v3 v4
du_writeHeapMem_850 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_850 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_844
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_860 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_502 (coe d_regs_494 (coe v1))
      (coe
         d_writeStackMem_740 (coe v0) (coe d_stackMem_496 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_498 (coe v1)) (coe d_halted_500 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_870 ~v0 v1 v2 v3 = du_writeLocToHeap_870 v1 v2 v3
du_writeLocToHeap_870 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_870 v0 v1 v2
  = coe
      C_mkLocState_502 (coe d_regs_494 (coe v0))
      (coe d_stackMem_496 (coe v0))
      (coe
         du_writeHeapMem_850 (coe d_heapMem_498 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_500 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_878 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_860 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_72 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_870 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_74 v5
               -> coe du_writeLocToHeap_870 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_78 v5 v6 v7
               -> coe du_writeLocToHeap_870 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_80 v5
               -> coe du_writeLocToHeap_870 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_928 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_966 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_966 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1006 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1006 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1026 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1026 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1054 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1086 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1364 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1416 a0 = ()
data T_LocSourceExt_1416
  = C_Loc_1420 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1422 T_AbstractReg_54 | C_IndRegSuc_1424 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1428 ~v0 v1 = du_sv'45'as'45'loc_1428 v1
du_sv'45'as'45'loc_1428 ::
  T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1428 v0
  = case coe v0 of
      C_SV'45'Ptr_72 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_SV'45'Tag_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Lit_78 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Code_80 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_LocSourceExt_1416 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1434 ~v0 v1 v2 = du_resolveSourceExt_1434 v1 v2
du_resolveSourceExt_1434 ::
  T_Registers_126 ->
  T_LocSourceExt_1416 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1434 v0 v1
  = case coe v1 of
      C_Loc_1420 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1422 v2
        -> coe
             du_sv'45'as'45'loc_1428 (coe du_readReg_154 (coe v0) (coe v2))
      C_IndRegSuc_1424 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1428 (coe du_readReg_154 (coe v0) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe du_sucLoc_84 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1464 a0 = ()
data T_Instr_1464
  = C_load_1468 T_AbstractReg_54 T_LocSourceExt_1416 |
    C_store_1470 T_LocSourceExt_1416 T_AbstractReg_54 |
    C_mov_1472 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_clear'45'frame_1480 v0 = coe d_clear'45'frame_768 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
d_clear'45'frame'45'aux_1482 ~v0 = du_clear'45'frame'45'aux_1482
du_clear'45'frame'45'aux_1482 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
du_clear'45'frame'45'aux_1482 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_762 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1484 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1486 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_1486 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_1488 ~v0 = du_readLoc_1488
du_readLoc_1488 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_1488 = coe du_readLoc_712
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1490 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_1490 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_1492 ~v0 = du_writeHeapMem_1492
du_writeHeapMem_1492 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_1492 = coe du_writeHeapMem_850
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_1494 ~v0 = du_writeHeapMem'45'aux_1494
du_writeHeapMem'45'aux_1494 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_1494 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_844 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_1496 v0 = coe d_writeLoc_878 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1498 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1500 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1500 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1502 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1504 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1506 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1508 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1510 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1510 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_1512 ~v0 = du_writeLocToHeap_1512
du_writeLocToHeap_1512 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_1512 = coe du_writeLocToHeap_870
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_1514 v0 = coe d_writeLocToStack_860 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_1516 v0 = coe d_writeStackMem_740 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_1518 ~v0 = du_writeStackMem'45'aux_1518
du_writeStackMem'45'aux_1518 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_1518 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_732 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'load'45'with'45'value_1520 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1520 v1 v2
du_exec'45'load'45'with'45'value_1520 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
du_exec'45'load'45'with'45'value_1520 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_502 (coe du_writeReg_168 (d_regs_494 (coe v3)) v0 v2)
                  (coe d_stackMem_496 (coe v3)) (coe d_heapMem_498 (coe v3))
                  (coe d_halted_500 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v2))
                  (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'via'45'resolved_1532 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1532 v1 v2
du_exec'45'load'45'via'45'resolved_1532 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'via'45'resolved_1532 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1520 v0
                  (coe du_readLoc_712 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v2))
                  (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'via'45'resolved_1544 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_878 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v3))
                  (coe d_stackMem_496 (coe v3)) (coe d_heapMem_498 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1554 ~v0 v1 = du_slot'45'base_1554 v1
du_slot'45'base_1554 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1554 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1428 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
d_exec'45'lea'45'indexed'45'via_1558 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1558 v1
du_exec'45'lea'45'indexed'45'via_1558 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
du_exec'45'lea'45'indexed'45'via_1558 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_502
                  (coe
                     du_writeReg_168 (d_regs_494 (coe v3)) (coe C_Input1_56)
                     (coe C_SV'45'Ptr_72 (coe du_offsetLoc_94 (coe v1) (coe v2))))
                  (coe d_stackMem_496 (coe v3)) (coe d_heapMem_498 (coe v3))
                  (coe d_halted_500 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v2))
                  (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_1570 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1570 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1570 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_1570 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1520 v0
                  (coe du_readLoc_712 (coe v3) (coe du_sucLoc_84 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v2))
                  (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_1582 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_878
                  (coe v0) (coe v4) (coe du_sucLoc_84 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v3))
                  (coe d_stackMem_496 (coe v3)) (coe d_heapMem_498 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1464 -> T_LocState_482 -> T_LocState_482
d_exec_1592 v0 v1
  = case coe v1 of
      C_load_1468 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1532 v2
                  (coe du_resolveSourceExt_1434 (coe d_regs_494 (coe v4)) (coe v3))
                  v4)
      C_store_1470 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1544 v0
                  (coe du_resolveSourceExt_1434 (coe d_regs_494 (coe v4)) (coe v2))
                  (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe v3)) v4)
      C_mov_1472 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_502
                  (coe
                     du_writeReg_168 (d_regs_494 (coe v4)) v2
                     (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe v3)))
                  (coe d_stackMem_496 (coe v4)) (coe d_heapMem_498 (coe v4))
                  (coe d_halted_500 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1618 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1624 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1464] -> T_LocState_482 -> T_LocState_482
d_execList_1626 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_500 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1626 (coe v0) (coe v4) (coe d_exec_1592 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_clear'45'frame_1658 v0 = coe d_clear'45'frame_768 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
d_clear'45'frame'45'aux_1660 ~v0 = du_clear'45'frame'45'aux_1660
du_clear'45'frame'45'aux_1660 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
du_clear'45'frame'45'aux_1660 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_762 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1662 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1664 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_1664 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_1666 ~v0 = du_readLoc_1666
du_readLoc_1666 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_1666 = coe du_readLoc_712
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1668 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_1668 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_1670 ~v0 = du_writeHeapMem_1670
du_writeHeapMem_1670 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_1670 = coe du_writeHeapMem_850
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_1672 ~v0 = du_writeHeapMem'45'aux_1672
du_writeHeapMem'45'aux_1672 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_1672 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_844 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_1674 v0 = coe d_writeLoc_878 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1676 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1678 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1678 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1680 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1682 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1684 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1686 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1688 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1688 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_1690 ~v0 = du_writeLocToHeap_1690
du_writeLocToHeap_1690 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_1690 = coe du_writeLocToHeap_870
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_1692 v0 = coe d_writeLocToStack_860 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_1694 v0 = coe d_writeStackMem_740 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_1696 ~v0 = du_writeStackMem'45'aux_1696
du_writeStackMem'45'aux_1696 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_1696 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_732 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1464 -> T_LocState_482 -> T_LocState_482
d_exec_1700 v0 = coe d_exec_1592 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
d_exec'45'lea'45'indexed'45'via_1702 ~v0
  = du_exec'45'lea'45'indexed'45'via_1702
du_exec'45'lea'45'indexed'45'via_1702 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
du_exec'45'lea'45'indexed'45'via_1702
  = coe du_exec'45'lea'45'indexed'45'via_1558
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1704 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1706 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_1708 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1708
du_exec'45'load'45'suc'45'via'45'resolved_1708 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_1708
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1570
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'via'45'resolved_1710 ~v0
  = du_exec'45'load'45'via'45'resolved_1710
du_exec'45'load'45'via'45'resolved_1710 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'via'45'resolved_1710
  = coe du_exec'45'load'45'via'45'resolved_1532
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'load'45'with'45'value_1712 ~v0
  = du_exec'45'load'45'with'45'value_1712
du_exec'45'load'45'with'45'value_1712 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
du_exec'45'load'45'with'45'value_1712
  = coe du_exec'45'load'45'with'45'value_1520
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_1714 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1582 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'via'45'resolved_1716 v0
  = coe d_exec'45'store'45'via'45'resolved_1544 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1464] -> T_LocState_482 -> T_LocState_482
d_execList_1718 v0 = coe d_execList_1626 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1720 ~v0 = du_slot'45'base_1720
du_slot'45'base_1720 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1720 = coe du_slot'45'base_1554
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_LocSourceExt_1416 -> Maybe T_StoredValue_68
d_resolved'45'readLoc_1722 ~v0 v1 v2
  = du_resolved'45'readLoc_1722 v1 v2
du_resolved'45'readLoc_1722 ::
  T_LocState_482 -> T_LocSourceExt_1416 -> Maybe T_StoredValue_68
du_resolved'45'readLoc_1722 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1434 (coe d_regs_494 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_712 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1752 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1822 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1898 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1928 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1984 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2036 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2088 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2104 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2122 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2136 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2154 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2220 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2244 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2272 = ()
data T_FlatCtrl_2272
  = C_c'45'label_2274 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2276 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'scratch'45'zero_2278 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2280 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'thunk_2282 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 Integer |
    C_c'45'ret_2284 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2286 = ()
data T_AbstractInstr_2286
  = C_mov'45'to'45'output_2288 | C_mov'45'to'45'input_2290 |
    C_mov'45'output'45'to'45'input2_2292 |
    C_mov'45'input2'45'to'45'output_2294 | C_load'45'indirect_2296 |
    C_load'45'indirect'45'suc_2298 |
    C_load'45'from'45'slot_2300 Integer |
    C_store'45'at'45'slot_2302 Integer | C_store'45'indirect_2304 |
    C_store'45'indirect'45'suc_2306 | C_lea'45'slot_2308 Integer |
    C_restore'45'input_2310 Integer |
    C_instr'45'alloc'45'stack_2312 Integer |
    C_instr'45'dealloc'45'stack_2314 Integer |
    C_instr'45'reclaim'45'to_2316 Integer |
    C_instr'45'push'45'frame_2318 Integer |
    C_instr'45'pop'45'frame_2320 | C_instr'45'call'45'closure_2322 |
    C_worklist'45'init_2324 Integer | C_worklist'45'push_2326 Integer |
    C_worklist'45'pop_2328 Integer | C_worklist'45'check_2330 Integer |
    C_instr'45'sigop_2336 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 |
    C_instr'45'load'45'const_2340 MAlonzo.Code.Once.Type.T_Type_112
                                  MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_instr'45'load'45'code'45'addr_2342 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2344 |
    C_instr'45'load'45'tag'45'lit_2346 Integer |
    C_instr'45'case'45'on'45'tag_2348 [T_AbstractInstr_2286]
                                      [T_AbstractInstr_2286] |
    C_instr'45'alloc'45'heap_2350 Integer |
    C_instr'45'loop_2352 [T_AbstractInstr_2286] |
    C_instr'45'reg'45'op_2354 T_RegOp_448 |
    C_instr'45'ctrl_2356 T_FlatCtrl_2272 |
    C_lea'45'indexed_2358 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2360 :: ()
d_AbstractTrace_2360 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2362 = ()
data T_TreeTrace_2362
  = C_ε_2364 | C_instr_2366 T_AbstractInstr_2286 |
    C__'9656'__2368 T_TreeTrace_2362 T_TreeTrace_2362 |
    C_branch_2370 Integer T_TreeTrace_2362 T_TreeTrace_2362 |
    C_call'45'sub_2372 T_TreeTrace_2362 |
    C_flat_2374 [T_AbstractInstr_2286]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2376 :: [T_AbstractInstr_2286] -> T_TreeTrace_2362
d_flatToTree_2376 v0
  = case coe v0 of
      [] -> coe C_ε_2364
      (:) v1 v2
        -> coe
             C__'9656'__2368 (coe C_instr_2366 (coe v1))
             (coe d_flatToTree_2376 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2382 :: T_TreeTrace_2362 -> [T_AbstractInstr_2286]
d_treeToFlat_2382 v0
  = case coe v0 of
      C_ε_2364 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2366 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2368 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2382 (coe v1)) (coe d_treeToFlat_2382 (coe v2))
      C_branch_2370 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2382 (coe v2)) (coe d_treeToFlat_2382 (coe v3))
      C_call'45'sub_2372 v1 -> coe d_treeToFlat_2382 (coe v1)
      C_flat_2374 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2398 ::
  Integer -> T_TreeTrace_2362 -> [T_AbstractInstr_2286]
d_treeToRunnable_2398 v0 v1
  = case coe v1 of
      C_ε_2364 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2366 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2368 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2398 (coe v0) (coe v2))
             (coe d_treeToRunnable_2398 (coe v0) (coe v3))
      C_branch_2370 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2398 (coe v0) (coe v3))
             (coe d_treeToRunnable_2398 (coe v0) (coe v4))
      C_call'45'sub_2372 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2326 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2398 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2328 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2374 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2428 ::
  Integer -> T_TreeTrace_2362 -> [T_AbstractInstr_2286]
d_treeToRunnableWithInit_2428 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2324 (coe v0))
      (coe d_treeToRunnable_2398 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_clear'45'frame_2472 v0 = coe d_clear'45'frame_768 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
d_clear'45'frame'45'aux_2474 ~v0 = du_clear'45'frame'45'aux_2474
du_clear'45'frame'45'aux_2474 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 -> Maybe T_StoredValue_68
du_clear'45'frame'45'aux_2474 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_762 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2476 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2478 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_2478 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_2480 ~v0 = du_readLoc_2480
du_readLoc_2480 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_2480 = coe du_readLoc_712
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2482 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_2482 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_2484 ~v0 = du_writeHeapMem_2484
du_writeHeapMem_2484 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_2484 = coe du_writeHeapMem_850
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_2486 ~v0 = du_writeHeapMem'45'aux_2486
du_writeHeapMem'45'aux_2486 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_2486 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_844 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_2488 v0 = coe d_writeLoc_878 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2490 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2492 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2492 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2494 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2496 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2498 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2500 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2502 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2502 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_2504 ~v0 = du_writeLocToHeap_2504
du_writeLocToHeap_2504 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_2504 = coe du_writeLocToHeap_870
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_2506 v0 = coe d_writeLocToStack_860 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_2508 v0 = coe d_writeStackMem_740 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_2510 ~v0 = du_writeStackMem'45'aux_2510
du_writeStackMem'45'aux_2510 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_2510 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_732 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1464 -> T_LocState_482 -> T_LocState_482
d_exec_2514 v0 = coe d_exec_1592 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
d_exec'45'lea'45'indexed'45'via_2516 ~v0
  = du_exec'45'lea'45'indexed'45'via_2516
du_exec'45'lea'45'indexed'45'via_2516 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
du_exec'45'lea'45'indexed'45'via_2516
  = coe du_exec'45'lea'45'indexed'45'via_1558
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2518 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2520 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_2522 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2522
du_exec'45'load'45'suc'45'via'45'resolved_2522 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_2522
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1570
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'via'45'resolved_2524 ~v0
  = du_exec'45'load'45'via'45'resolved_2524
du_exec'45'load'45'via'45'resolved_2524 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'via'45'resolved_2524
  = coe du_exec'45'load'45'via'45'resolved_1532
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'load'45'with'45'value_2526 ~v0
  = du_exec'45'load'45'with'45'value_2526
du_exec'45'load'45'with'45'value_2526 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
du_exec'45'load'45'with'45'value_2526
  = coe du_exec'45'load'45'with'45'value_1520
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_2528 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1582 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'via'45'resolved_2530 v0
  = coe d_exec'45'store'45'via'45'resolved_1544 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1464] -> T_LocState_482 -> T_LocState_482
d_execList_2532 v0 = coe d_execList_1626 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2534 ~v0 = du_slot'45'base_2534
du_slot'45'base_2534 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2534 = coe du_slot'45'base_1554
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2538 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2540 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2542 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2544 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2546 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2548 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2550 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1416 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2552 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2554 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2556 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2558 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2560 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2562 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_LocSourceExt_1416 -> Maybe T_StoredValue_68
d_resolved'45'readLoc_2564 ~v0 = du_resolved'45'readLoc_2564
du_resolved'45'readLoc_2564 ::
  T_LocState_482 -> T_LocSourceExt_1416 -> Maybe T_StoredValue_68
du_resolved'45'readLoc_2564 = coe du_resolved'45'readLoc_1722
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2566 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2566 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2566 ::
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2566 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe du_writeReg_168 (d_regs_494 (coe v1)) (coe C_Output_60) v3)
                (coe d_stackMem_496 (coe v1)) (coe d_heapMem_498 (coe v1))
                (coe d_halted_500 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502 (coe d_regs_494 (coe v1))
                (coe d_stackMem_496 (coe v1)) (coe d_heapMem_498 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2578 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2578 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2578 ::
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2578 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe du_writeReg_168 (d_regs_494 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_496 (coe v1)) (coe d_heapMem_498 (coe v1))
                (coe d_halted_500 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502 (coe d_regs_494 (coe v1))
                (coe d_stackMem_496 (coe v1)) (coe d_heapMem_498 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2596 ::
  T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2596 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2602 ::
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2602 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2610 ::
  T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2610 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2616 ::
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2616 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68
d_unit'45'storedvalue_2618 ~v0 = du_unit'45'storedvalue_2618
du_unit'45'storedvalue_2618 :: T_StoredValue_68
du_unit'45'storedvalue_2618
  = coe
      C_SV'45'Lit_78 (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2624 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2624 v3 v4
du_combine'45'typed_2624 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2624 v0 v1
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
d_readTyped'45'int_2630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 -> Maybe Integer
d_readTyped'45'int_2630 ~v0 v1 = du_readTyped'45'int_2630 v1
du_readTyped'45'int_2630 :: Maybe T_StoredValue_68 -> Maybe Integer
du_readTyped'45'int_2630 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                C_SV'45'Lit_78 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_198
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-pair
d_readTyped'45'pair_2638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_68 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_2638 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'pair_2638 v3 v4 v5 v6
du_readTyped'45'pair_2638 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_68 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2638 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> case coe v5 of
                C_SV'45'Ptr_72 v6
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              C_SV'45'Ptr_72 v8
                                -> coe du_combine'45'typed_2624 (coe v0 v6) (coe v1 v8)
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_68 -> Maybe AgdaAny
d_readReg'45'typed_2654 ~v0 v1 v2 = du_readReg'45'typed_2654 v1 v2
du_readReg'45'typed_2654 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_68 -> Maybe AgdaAny
du_readReg'45'typed_2654 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C_Int_136
           -> case coe v1 of
                C_SV'45'Lit_78 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_198
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped
d_readTyped_2660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> Maybe AgdaAny
d_readTyped_2660 ~v0 v1 v2 v3 = du_readTyped_2660 v1 v2 v3
du_readTyped_2660 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> Maybe AgdaAny
du_readTyped_2660 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
           -> coe
                du_readTyped'45'pair_2638
                (coe (\ v6 -> coe du_readTyped_2660 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2660 (coe v5) (coe v6) (coe v2)))
                (coe du_readLoc_712 (coe v2) (coe v1))
                (coe du_readLoc_712 (coe v2) (coe du_sucLoc_84 (coe v1)))
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe
                du_readTyped'45'int_2630 (coe du_readLoc_712 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2690
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> T_StoredValue_68
d_pure'45'sigop'45'output_2696 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_2718 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v2))
      (coe
         du_sv'45'as'45'loc_1428
         (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_68
d_pure'45'sigop'45'out'45'val_2702 ~v0 ~v1 v2 v3 v4 v5
  = du_pure'45'sigop'45'out'45'val_2702 v2 v3 v4 v5
du_pure'45'sigop'45'out'45'val_2702 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_68
du_pure'45'sigop'45'out'45'val_2702 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_SV'45'Lit_78 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.SigOp.Info.du_semM_188 v1 v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2618
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_2718 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pure'45'sigop'45'out'45'val_2702 (coe v2) (coe v3) (coe v7)
                    (coe du_readTyped_2660 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'sigop'45'out'45'val_2702 (coe v2) (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2654 (coe v1)
                       (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2690 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> T_StoredValue_68
d_exec'45'sigop'45'output'45'of_2754 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_pure'45'sigop'45'output_2696 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe du_unit'45'storedvalue_2618
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe du_unit'45'storedvalue_2618
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> T_StoredValue_68
d_exec'45'sigop'45'output_2764 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2754 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> Bool
d_exec'45'sigop'45'halts'45'of_2774 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2774 v3
du_exec'45'sigop'45'halts'45'of_2774 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> Bool
du_exec'45'sigop'45'halts'45'of_2774 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> Bool
d_exec'45'sigop'45'halts_2780 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2780 v3
du_exec'45'sigop'45'halts_2780 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 -> Bool
du_exec'45'sigop'45'halts_2780 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2774
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> Maybe T_StoredValue_68
d_case'45'tag'45'at_2786 ~v0 v1 = du_case'45'tag'45'at_2786 v1
du_case'45'tag'45'at_2786 ::
  T_LocState_482 -> Maybe T_StoredValue_68
du_case'45'tag'45'at_2786 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1428
              (coe d_input1_140 (coe d_regs_494 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_712 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.BodyRunner
d_BodyRunner_2800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_2800 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_2802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_LocState_482 -> T_LocState_482
d_loop'45'reanchor'45'loc_2802 ~v0 v1 v2
  = du_loop'45'reanchor'45'loc_2802 v1 v2
du_loop'45'reanchor'45'loc_2802 ::
  T_LocState_482 -> T_LocState_482 -> T_LocState_482
du_loop'45'reanchor'45'loc_2802 v0 v1
  = coe
      C_mkLocState_502 (coe d_regs_494 (coe v1))
      (coe d_stackMem_496 (coe v0)) (coe d_heapMem_498 (coe v1))
      (coe d_halted_500 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_2808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_568 -> T_AllocState_568 -> T_AllocState_568
d_loop'45'reanchor'45'alloc_2808 ~v0 v1 v2
  = du_loop'45'reanchor'45'alloc_2808 v1 v2
du_loop'45'reanchor'45'alloc_2808 ::
  T_AllocState_568 -> T_AllocState_568 -> T_AllocState_568
du_loop'45'reanchor'45'alloc_2808 v0 v1
  = coe
      C_mkAllocState_660 (coe d_current'45'frame_648 (coe v0))
      (coe d_saved'45'frames_650 (coe v1))
      (coe d_frame'45'slots_652 (coe v1))
      (coe d_next'45'slot_654 (coe v0))
      (coe d_next'45'heap'45'ref_656 (coe v1))
      (coe d_block'45'size_658 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_2814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_482 ->
   T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_2814 ~v0 v1 v2 v3 v4
  = du_exec'45'loop'45'run_2814 v1 v2 v3 v4
du_exec'45'loop'45'run_2814 ::
  (T_LocState_482 ->
   T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_2814 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502 (coe d_regs_494 (coe v2))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_500 (coe v2) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                   else (let v6 = d_scratch_146 (coe d_regs_494 (coe v2)) in
                         coe
                           (let v7
                                  = coe
                                      du_exec'45'loop'45'run_2814 (coe v0) (coe v4)
                                      (coe
                                         du_loop'45'reanchor'45'loc_2802 (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe v0 v2 v3)))
                                      (coe
                                         du_loop'45'reanchor'45'alloc_2808 (coe v3)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe v0 v2 v3))) in
                            coe
                              (case coe v6 of
                                 C_SV'45'Tag_74 v8
                                   -> case coe v8 of
                                        0 -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                               (coe v3)
                                        _ -> coe v7
                                 _ -> coe v7)))))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2286 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2870 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2288
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2290
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_2292
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Input2_58)
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_2294
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input2_58)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_load'45'indirect_2296
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1532 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1428
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2298
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1570 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1428
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2300 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2566
             (coe
                du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2302 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_878 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_store'45'indirect_2304
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1544 v0
                (coe
                   du_sv'45'as'45'loc_1428
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2306
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1582 v0
                (coe
                   du_sv'45'as'45'loc_1428
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_lea'45'slot_2308 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe
                      C_SV'45'Ptr_72
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_648 (coe v3)) (coe v4))))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_restore'45'input_2310 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2578
             (coe
                du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2312 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_660 (coe d_current'45'frame_648 (coe v3))
                (coe d_saved'45'frames_650 (coe v3))
                (coe d_frame'45'slots_652 (coe v3))
                (coe addInt (coe d_next'45'slot_654 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_656 (coe v3))
                (coe d_block'45'size_658 (coe v3)))
      C_instr'45'dealloc'45'stack_2314 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2316 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_660 (coe d_current'45'frame_648 (coe v3))
                (coe d_saved'45'frames_650 (coe v3))
                (coe d_frame'45'slots_652 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_656 (coe v3))
                (coe d_block'45'size_658 (coe v3)))
      C_instr'45'push'45'frame_2318 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2320
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2322
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2324 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2326 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_878 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_worklist'45'pop_2328 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2566
             (coe
                du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2330 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2336 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (d_exec'45'sigop'45'output_2764
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe du_exec'45'sigop'45'halts_2780 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2340 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Lit_78 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2342 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Code_80 (coe v4)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2344
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2346 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Tag_74 (coe v4)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2348 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2876 (coe v0)
             (coe du_case'45'tag'45'at_2786 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2350 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (coe
                      C_SV'45'Ptr_72
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_656 (coe v3)))))))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe d_halted_500 (coe v2)))
             (coe
                C_mkAllocState_660 (coe d_current'45'frame_648 (coe v3))
                (coe d_saved'45'frames_650 (coe v3))
                (coe d_frame'45'slots_652 (coe v3))
                (coe d_next'45'slot_654 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_656 (coe v3)))))
                (coe
                   d_size'45'with_556 (coe v4)
                   (coe d_next'45'heap'45'ref_656 (coe v3))
                   (coe d_block'45'size_658 (coe v3))))
      C_instr'45'loop_2352 v4
        -> coe
             d_exec'45'loop_2874 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2354 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_522 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2356 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2358 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1558
                (coe
                   du_slot'45'base_1554
                   (coe
                      du_readLoc_712 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_648 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_476
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Scratch_62)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2286] ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2872 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_500 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2872 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2870 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2870 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2286] ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2874 v0 v1 v2 v3 v4
  = coe
      du_exec'45'loop'45'run_2814
      (coe d_exec'45'trace_2872 (coe v0) (coe v2)) (coe v1) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_2876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  [T_AbstractInstr_2286] ->
  [T_AbstractInstr_2286] ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2876 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_72 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_502 (coe d_regs_494 (coe v4))
                       (coe d_stackMem_496 (coe v4)) (coe d_heapMem_498 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Tag_74 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_2872 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2872 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_78 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_502 (coe d_regs_494 (coe v4))
                       (coe d_stackMem_496 (coe v4)) (coe d_heapMem_498 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Code_80 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_502 (coe d_regs_494 (coe v4))
                       (coe d_stackMem_496 (coe v4)) (coe d_heapMem_498 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502 (coe d_regs_494 (coe v4))
                (coe d_stackMem_496 (coe v4)) (coe d_heapMem_498 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_3166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2286 ->
  [T_AbstractInstr_2286] ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3166 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2286 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3212 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2286 -> ()) -> [T_AbstractInstr_2286] -> ()
d_AllI_3246 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_568 -> AgdaAny) ->
  (T_AbstractInstr_2286 -> ()) ->
  (T_AbstractInstr_2286 ->
   T_LocState_482 ->
   T_AllocState_568 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2286] ->
  AgdaAny ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3274 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_568 -> AgdaAny) ->
  (T_AbstractInstr_2286 -> ()) ->
  (T_AbstractInstr_2286 ->
   T_LocState_482 ->
   T_AllocState_568 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2286] ->
  [T_AbstractInstr_2286] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3364 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_AllocState_568 -> Integer -> Maybe Integer
d_getTag_3496 ~v0 v1 v2 v3 = du_getTag_3496 v1 v2 v3
du_getTag_3496 ::
  T_LocState_482 -> T_AllocState_568 -> Integer -> Maybe Integer
du_getTag_3496 v0 v1 v2
  = let v3
          = coe d_stackMem_496 v0 (d_current'45'frame_648 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2362 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3520 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2364
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2366 v4
        -> let v5 = d_halted_500 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2870 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2368 v4 v5
        -> let v6 = d_halted_500 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3520 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3520 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3520 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2370 v4 v5 v6
        -> let v7 = d_halted_500 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_496 v2 (d_current'45'frame_648 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3520 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3520 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3520 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3520 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3520 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2372 v4
        -> let v5 = d_halted_500 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3520 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2374 v4
        -> coe d_exec'45'trace_2872 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3680 ::
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3680 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2362 ->
  T_TreeTrace_2362 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3698 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2286 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3744 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2362 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3784 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2286] ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3824 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2286] ->
  [T_AbstractInstr_2286] ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3844 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3902
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2362 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3910 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3910
du_exec'45'tree'45'flat'45'equiv'45'simple_3910 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3910
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
