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
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_758 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_758 v3 v4 v5
du_writeHeapMem'45'aux_758 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_758 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_764 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_764 v1 v2 v3 v4
du_writeHeapMem_764 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_764 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_758
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_774 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_502 (coe d_regs_494 (coe v1))
      (coe
         d_writeStackMem_740 (coe v0) (coe d_stackMem_496 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_498 (coe v1)) (coe d_halted_500 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_784 ~v0 v1 v2 v3 = du_writeLocToHeap_784 v1 v2 v3
du_writeLocToHeap_784 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_784 v0 v1 v2
  = coe
      C_mkLocState_502 (coe d_regs_494 (coe v0))
      (coe d_stackMem_496 (coe v0))
      (coe
         du_writeHeapMem_764 (coe d_heapMem_498 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_500 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_792 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_774 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_72 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_784 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_74 v5
               -> coe du_writeLocToHeap_784 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_78 v5 v6 v7
               -> coe du_writeLocToHeap_784 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_80 v5
               -> coe du_writeLocToHeap_784 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_842 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_880 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_920 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_920 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_940 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_940 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_968 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_968 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1000 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1000 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1278 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1330 a0 = ()
data T_LocSourceExt_1330
  = C_Loc_1334 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1336 T_AbstractReg_54 | C_IndRegSuc_1338 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1342 ~v0 v1 = du_sv'45'as'45'loc_1342 v1
du_sv'45'as'45'loc_1342 ::
  T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1342 v0
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
d_resolveSourceExt_1348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_LocSourceExt_1330 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1348 ~v0 v1 v2 = du_resolveSourceExt_1348 v1 v2
du_resolveSourceExt_1348 ::
  T_Registers_126 ->
  T_LocSourceExt_1330 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1348 v0 v1
  = case coe v1 of
      C_Loc_1334 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1336 v2
        -> coe
             du_sv'45'as'45'loc_1342 (coe du_readReg_154 (coe v0) (coe v2))
      C_IndRegSuc_1338 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1342 (coe du_readReg_154 (coe v0) (coe v2)) in
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
d_Instr_1378 a0 = ()
data T_Instr_1378
  = C_load_1382 T_AbstractReg_54 T_LocSourceExt_1330 |
    C_store_1384 T_LocSourceExt_1330 T_AbstractReg_54 |
    C_mov_1386 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1394 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_1394 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_1396 ~v0 = du_readLoc_1396
du_readLoc_1396 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_1396 = coe du_readLoc_712
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1398 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_1398 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_1400 ~v0 = du_writeHeapMem_1400
du_writeHeapMem_1400 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_1400 = coe du_writeHeapMem_764
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_1402 ~v0 = du_writeHeapMem'45'aux_1402
du_writeHeapMem'45'aux_1402 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_1402 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_758 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_1404 v0 = coe d_writeLoc_792 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1406 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1408 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1408 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1410 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1412 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1412 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1414 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1416 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1418 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1418 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_1420 ~v0 = du_writeLocToHeap_1420
du_writeLocToHeap_1420 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_1420 = coe du_writeLocToHeap_784
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_1422 v0 = coe d_writeLocToStack_774 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_1424 v0 = coe d_writeStackMem_740 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_1426 ~v0 = du_writeStackMem'45'aux_1426
du_writeStackMem'45'aux_1426 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_1426 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_732 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'load'45'with'45'value_1428 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1428 v1 v2
du_exec'45'load'45'with'45'value_1428 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
du_exec'45'load'45'with'45'value_1428 v0 v1
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
d_exec'45'load'45'via'45'resolved_1440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'via'45'resolved_1440 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1440 v1 v2
du_exec'45'load'45'via'45'resolved_1440 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'via'45'resolved_1440 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1428 v0
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
d_exec'45'store'45'via'45'resolved_1452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'via'45'resolved_1452 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_792 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_502 (coe d_regs_494 (coe v3))
                  (coe d_stackMem_496 (coe v3)) (coe d_heapMem_498 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1462 ~v0 v1 = du_slot'45'base_1462 v1
du_slot'45'base_1462 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1462 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1342 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
d_exec'45'lea'45'indexed'45'via_1466 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1466 v1
du_exec'45'lea'45'indexed'45'via_1466 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
du_exec'45'lea'45'indexed'45'via_1466 v0
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
d_exec'45'load'45'suc'45'via'45'resolved_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_1478 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1478 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1478 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_1478 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1428 v0
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
d_exec'45'store'45'suc'45'via'45'resolved_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_1490 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_792
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
d_exec_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1378 -> T_LocState_482 -> T_LocState_482
d_exec_1500 v0 v1
  = case coe v1 of
      C_load_1382 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1440 v2
                  (coe du_resolveSourceExt_1348 (coe d_regs_494 (coe v4)) (coe v3))
                  v4)
      C_store_1384 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1452 v0
                  (coe du_resolveSourceExt_1348 (coe d_regs_494 (coe v4)) (coe v2))
                  (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe v3)) v4)
      C_mov_1386 v2 v3
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
d_exec'45'load'45'just_1526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1526 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1532 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1378] -> T_LocState_482 -> T_LocState_482
d_execList_1534 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_500 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1534 (coe v0) (coe v4) (coe d_exec_1500 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1566 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_1566 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_1568 ~v0 = du_readLoc_1568
du_readLoc_1568 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_1568 = coe du_readLoc_712
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1570 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_1570 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_1572 ~v0 = du_writeHeapMem_1572
du_writeHeapMem_1572 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_1572 = coe du_writeHeapMem_764
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_1574 ~v0 = du_writeHeapMem'45'aux_1574
du_writeHeapMem'45'aux_1574 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_1574 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_758 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_1576 v0 = coe d_writeLoc_792 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1578 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1580 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1580 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1582 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1584 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1584 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1586 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1588 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1590 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1590 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_1592 ~v0 = du_writeLocToHeap_1592
du_writeLocToHeap_1592 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_1592 = coe du_writeLocToHeap_784
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_1594 v0 = coe d_writeLocToStack_774 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_1596 v0 = coe d_writeStackMem_740 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_1598 ~v0 = du_writeStackMem'45'aux_1598
du_writeStackMem'45'aux_1598 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_1598 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_732 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1378 -> T_LocState_482 -> T_LocState_482
d_exec_1602 v0 = coe d_exec_1500 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
d_exec'45'lea'45'indexed'45'via_1604 ~v0
  = du_exec'45'lea'45'indexed'45'via_1604
du_exec'45'lea'45'indexed'45'via_1604 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
du_exec'45'lea'45'indexed'45'via_1604
  = coe du_exec'45'lea'45'indexed'45'via_1466
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1606 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1608 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_1610 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1610
du_exec'45'load'45'suc'45'via'45'resolved_1610 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_1610
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1478
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'via'45'resolved_1612 ~v0
  = du_exec'45'load'45'via'45'resolved_1612
du_exec'45'load'45'via'45'resolved_1612 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'via'45'resolved_1612
  = coe du_exec'45'load'45'via'45'resolved_1440
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'load'45'with'45'value_1614 ~v0
  = du_exec'45'load'45'with'45'value_1614
du_exec'45'load'45'with'45'value_1614 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
du_exec'45'load'45'with'45'value_1614
  = coe du_exec'45'load'45'with'45'value_1428
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_1616 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1490 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'via'45'resolved_1618 v0
  = coe d_exec'45'store'45'via'45'resolved_1452 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1378] -> T_LocState_482 -> T_LocState_482
d_execList_1620 v0 = coe d_execList_1534 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1622 ~v0 = du_slot'45'base_1622
du_slot'45'base_1622 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1622 = coe du_slot'45'base_1462
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_LocSourceExt_1330 -> Maybe T_StoredValue_68
d_resolved'45'readLoc_1624 ~v0 v1 v2
  = du_resolved'45'readLoc_1624 v1 v2
du_resolved'45'readLoc_1624 ::
  T_LocState_482 -> T_LocSourceExt_1330 -> Maybe T_StoredValue_68
du_resolved'45'readLoc_1624 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1348 (coe d_regs_494 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_712 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1654 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1724 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1800 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1830 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1886 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1938 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1990 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2006 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2006 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2024 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2024 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2038 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2056 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2056 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2122 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2146 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2174 = ()
data T_FlatCtrl_2174
  = C_c'45'label_2176 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2178 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'scratch'45'zero_2180 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2182 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'thunk_2184 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 Integer |
    C_c'45'ret_2186 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2188 = ()
data T_AbstractInstr_2188
  = C_mov'45'to'45'output_2190 | C_mov'45'to'45'input_2192 |
    C_mov'45'output'45'to'45'input2_2194 |
    C_mov'45'input2'45'to'45'output_2196 | C_load'45'indirect_2198 |
    C_load'45'indirect'45'suc_2200 |
    C_load'45'from'45'slot_2202 Integer |
    C_store'45'at'45'slot_2204 Integer | C_store'45'indirect_2206 |
    C_store'45'indirect'45'suc_2208 | C_lea'45'slot_2210 Integer |
    C_restore'45'input_2212 Integer |
    C_instr'45'alloc'45'stack_2214 Integer |
    C_instr'45'dealloc'45'stack_2216 Integer |
    C_instr'45'reclaim'45'to_2218 Integer |
    C_instr'45'push'45'frame_2220 Integer |
    C_instr'45'pop'45'frame_2222 | C_instr'45'call'45'closure_2224 |
    C_worklist'45'init_2226 Integer | C_worklist'45'push_2228 Integer |
    C_worklist'45'pop_2230 Integer | C_worklist'45'check_2232 Integer |
    C_instr'45'sigop_2238 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 |
    C_instr'45'load'45'const_2242 MAlonzo.Code.Once.Type.T_Type_112
                                  MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_instr'45'load'45'code'45'addr_2244 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2246 |
    C_instr'45'load'45'tag'45'lit_2248 Integer |
    C_instr'45'case'45'on'45'tag_2250 [T_AbstractInstr_2188]
                                      [T_AbstractInstr_2188] |
    C_instr'45'alloc'45'heap_2252 Integer |
    C_instr'45'loop_2254 [T_AbstractInstr_2188] |
    C_instr'45'reg'45'op_2256 T_RegOp_448 |
    C_instr'45'ctrl_2258 T_FlatCtrl_2174 |
    C_lea'45'indexed_2260 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2262 :: ()
d_AbstractTrace_2262 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2264 = ()
data T_TreeTrace_2264
  = C_ε_2266 | C_instr_2268 T_AbstractInstr_2188 |
    C__'9656'__2270 T_TreeTrace_2264 T_TreeTrace_2264 |
    C_branch_2272 Integer T_TreeTrace_2264 T_TreeTrace_2264 |
    C_call'45'sub_2274 T_TreeTrace_2264 |
    C_flat_2276 [T_AbstractInstr_2188]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2278 :: [T_AbstractInstr_2188] -> T_TreeTrace_2264
d_flatToTree_2278 v0
  = case coe v0 of
      [] -> coe C_ε_2266
      (:) v1 v2
        -> coe
             C__'9656'__2270 (coe C_instr_2268 (coe v1))
             (coe d_flatToTree_2278 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2284 :: T_TreeTrace_2264 -> [T_AbstractInstr_2188]
d_treeToFlat_2284 v0
  = case coe v0 of
      C_ε_2266 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2268 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2270 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2284 (coe v1)) (coe d_treeToFlat_2284 (coe v2))
      C_branch_2272 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2284 (coe v2)) (coe d_treeToFlat_2284 (coe v3))
      C_call'45'sub_2274 v1 -> coe d_treeToFlat_2284 (coe v1)
      C_flat_2276 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2300 ::
  Integer -> T_TreeTrace_2264 -> [T_AbstractInstr_2188]
d_treeToRunnable_2300 v0 v1
  = case coe v1 of
      C_ε_2266 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2268 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2270 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2300 (coe v0) (coe v2))
             (coe d_treeToRunnable_2300 (coe v0) (coe v3))
      C_branch_2272 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2300 (coe v0) (coe v3))
             (coe d_treeToRunnable_2300 (coe v0) (coe v4))
      C_call'45'sub_2274 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2228 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2300 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2230 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2276 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2330 ::
  Integer -> T_TreeTrace_2264 -> [T_AbstractInstr_2188]
d_treeToRunnableWithInit_2330 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2226 (coe v0))
      (coe d_treeToRunnable_2300 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2374 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_2374 v0 v1 = coe d_heapMem_498 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_2376 ~v0 = du_readLoc_2376
du_readLoc_2376 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_2376 = coe du_readLoc_712
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2378 ::
  T_LocState_482 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_2378 v0 v1 v2 = coe d_stackMem_496 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_2380 ~v0 = du_writeHeapMem_2380
du_writeHeapMem_2380 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_2380 = coe du_writeHeapMem_764
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_2382 ~v0 = du_writeHeapMem'45'aux_2382
du_writeHeapMem'45'aux_2382 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_2382 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_758 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLoc_2384 v0 = coe d_writeLoc_792 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2386 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2388 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2388 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2390 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2392 ::
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
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2392 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2394 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2396 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2398 ::
  T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2398 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
d_writeLocToHeap_2400 ~v0 = du_writeLocToHeap_2400
du_writeLocToHeap_2400 ::
  T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_482
du_writeLocToHeap_2400 = coe du_writeLocToHeap_784
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_482
d_writeLocToStack_2402 v0 = coe d_writeLocToStack_774 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_2404 v0 = coe d_writeStackMem_740 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_2406 ~v0 = du_writeStackMem'45'aux_2406
du_writeStackMem'45'aux_2406 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_2406 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_732 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1378 -> T_LocState_482 -> T_LocState_482
d_exec_2410 v0 = coe d_exec_1500 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
d_exec'45'lea'45'indexed'45'via_2412 ~v0
  = du_exec'45'lea'45'indexed'45'via_2412
du_exec'45'lea'45'indexed'45'via_2412 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_482 -> T_LocState_482
du_exec'45'lea'45'indexed'45'via_2412
  = coe du_exec'45'lea'45'indexed'45'via_1466
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2414 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2416 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_2418 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2418
du_exec'45'load'45'suc'45'via'45'resolved_2418 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_2418
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1478
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
d_exec'45'load'45'via'45'resolved_2420 ~v0
  = du_exec'45'load'45'via'45'resolved_2420
du_exec'45'load'45'via'45'resolved_2420 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> T_LocState_482
du_exec'45'load'45'via'45'resolved_2420
  = coe du_exec'45'load'45'via'45'resolved_1440
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'load'45'with'45'value_2422 ~v0
  = du_exec'45'load'45'with'45'value_2422
du_exec'45'load'45'with'45'value_2422 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
du_exec'45'load'45'with'45'value_2422
  = coe du_exec'45'load'45'with'45'value_1428
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_2424 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1490 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_482 -> T_LocState_482
d_exec'45'store'45'via'45'resolved_2426 v0
  = coe d_exec'45'store'45'via'45'resolved_1452 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1378] -> T_LocState_482 -> T_LocState_482
d_execList_2428 v0 = coe d_execList_1534 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2430 ~v0 = du_slot'45'base_2430
du_slot'45'base_2430 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2430 = coe du_slot'45'base_1462
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2434 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  T_LocState_482 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2436 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2438 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2440 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2442 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2444 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2446 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1330 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2448 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2450 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2452 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2454 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_482 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2456 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 ->
  T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2458 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_LocSourceExt_1330 -> Maybe T_StoredValue_68
d_resolved'45'readLoc_2460 ~v0 = du_resolved'45'readLoc_2460
du_resolved'45'readLoc_2460 ::
  T_LocState_482 -> T_LocSourceExt_1330 -> Maybe T_StoredValue_68
du_resolved'45'readLoc_2460 = coe du_resolved'45'readLoc_1624
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2462 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2462 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2462 ::
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2462 v0 v1 v2
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
d_exec'45'restore'45'input'45'with'45'value_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2474 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2474 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2474 ::
  Maybe T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2474 v0 v1 v2
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
d_exec'45'load'45'from'45'slot'45'just_2492 ::
  T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2492 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2498 ::
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2498 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2506 ::
  T_StoredValue_68 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2506 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2512 ::
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2512 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68
d_unit'45'storedvalue_2514 ~v0 = du_unit'45'storedvalue_2514
du_unit'45'storedvalue_2514 :: T_StoredValue_68
du_unit'45'storedvalue_2514
  = coe
      C_SV'45'Lit_78 (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2520 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2520 v3 v4
du_combine'45'typed_2520 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2520 v0 v1
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
d_readTyped'45'int_2526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 -> Maybe Integer
d_readTyped'45'int_2526 ~v0 v1 = du_readTyped'45'int_2526 v1
du_readTyped'45'int_2526 :: Maybe T_StoredValue_68 -> Maybe Integer
du_readTyped'45'int_2526 v0
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
d_readTyped'45'pair_2534 ::
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
d_readTyped'45'pair_2534 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'pair_2534 v3 v4 v5 v6
du_readTyped'45'pair_2534 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_68 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2534 v0 v1 v2 v3
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
                                -> coe du_combine'45'typed_2520 (coe v0 v6) (coe v1 v8)
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_68 -> Maybe AgdaAny
d_readReg'45'typed_2550 ~v0 v1 v2 = du_readReg'45'typed_2550 v1 v2
du_readReg'45'typed_2550 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_68 -> Maybe AgdaAny
du_readReg'45'typed_2550 v0 v1
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
d_readTyped_2556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> Maybe AgdaAny
d_readTyped_2556 ~v0 v1 v2 v3 = du_readTyped_2556 v1 v2 v3
du_readTyped_2556 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_482 -> Maybe AgdaAny
du_readTyped_2556 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
           -> coe
                du_readTyped'45'pair_2534
                (coe (\ v6 -> coe du_readTyped_2556 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2556 (coe v5) (coe v6) (coe v2)))
                (coe du_readLoc_712 (coe v2) (coe v1))
                (coe du_readLoc_712 (coe v2) (coe du_sucLoc_84 (coe v1)))
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe
                du_readTyped'45'int_2526 (coe du_readLoc_712 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2586
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> T_StoredValue_68
d_pure'45'sigop'45'output_2592 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_2614 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v2))
      (coe
         du_sv'45'as'45'loc_1342
         (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_68
d_pure'45'sigop'45'out'45'val_2598 ~v0 ~v1 v2 v3 v4 v5
  = du_pure'45'sigop'45'out'45'val_2598 v2 v3 v4 v5
du_pure'45'sigop'45'out'45'val_2598 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_68
du_pure'45'sigop'45'out'45'val_2598 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_SV'45'Lit_78 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.SigOp.Info.du_semM_188 v1 v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2514
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_2614 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pure'45'sigop'45'out'45'val_2598 (coe v2) (coe v3) (coe v7)
                    (coe du_readTyped_2556 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'sigop'45'out'45'val_2598 (coe v2) (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2550 (coe v1)
                       (coe du_readReg_154 (coe d_regs_494 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2586 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> T_StoredValue_68
d_exec'45'sigop'45'output'45'of_2650 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_pure'45'sigop'45'output_2592 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe du_unit'45'storedvalue_2514
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe du_unit'45'storedvalue_2514
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> T_StoredValue_68
d_exec'45'sigop'45'output_2660 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2650 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> Bool
d_exec'45'sigop'45'halts'45'of_2670 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2670 v3
du_exec'45'sigop'45'halts'45'of_2670 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> Bool
du_exec'45'sigop'45'halts'45'of_2670 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_482 -> Bool
d_exec'45'sigop'45'halts_2676 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2676 v3
du_exec'45'sigop'45'halts_2676 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 -> Bool
du_exec'45'sigop'45'halts_2676 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2670
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> Maybe T_StoredValue_68
d_case'45'tag'45'at_2682 ~v0 v1 = du_case'45'tag'45'at_2682 v1
du_case'45'tag'45'at_2682 ::
  T_LocState_482 -> Maybe T_StoredValue_68
du_case'45'tag'45'at_2682 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1342
              (coe d_input1_140 (coe d_regs_494 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_712 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.BodyRunner
d_BodyRunner_2696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_2696 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_2698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_LocState_482 -> T_LocState_482
d_loop'45'reanchor'45'loc_2698 ~v0 v1 v2
  = du_loop'45'reanchor'45'loc_2698 v1 v2
du_loop'45'reanchor'45'loc_2698 ::
  T_LocState_482 -> T_LocState_482 -> T_LocState_482
du_loop'45'reanchor'45'loc_2698 v0 v1
  = coe
      C_mkLocState_502 (coe d_regs_494 (coe v1))
      (coe d_stackMem_496 (coe v0)) (coe d_heapMem_498 (coe v1))
      (coe d_halted_500 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_2704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_568 -> T_AllocState_568 -> T_AllocState_568
d_loop'45'reanchor'45'alloc_2704 ~v0 v1 v2
  = du_loop'45'reanchor'45'alloc_2704 v1 v2
du_loop'45'reanchor'45'alloc_2704 ::
  T_AllocState_568 -> T_AllocState_568 -> T_AllocState_568
du_loop'45'reanchor'45'alloc_2704 v0 v1
  = coe
      C_mkAllocState_660 (coe d_current'45'frame_648 (coe v0))
      (coe d_saved'45'frames_650 (coe v1))
      (coe d_frame'45'slots_652 (coe v1))
      (coe d_next'45'slot_654 (coe v0))
      (coe d_next'45'heap'45'ref_656 (coe v1))
      (coe d_block'45'size_658 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_2710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_482 ->
   T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_2710 ~v0 v1 v2 v3 v4
  = du_exec'45'loop'45'run_2710 v1 v2 v3 v4
du_exec'45'loop'45'run_2710 ::
  (T_LocState_482 ->
   T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_2710 v0 v1 v2 v3
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
                                      du_exec'45'loop'45'run_2710 (coe v0) (coe v4)
                                      (coe
                                         du_loop'45'reanchor'45'loc_2698 (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe v0 v2 v3)))
                                      (coe
                                         du_loop'45'reanchor'45'alloc_2704 (coe v3)
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
d_exec'45'abstract_2766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2188 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2766 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2190
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
      C_mov'45'to'45'input_2192
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
      C_mov'45'output'45'to'45'input2_2194
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
      C_mov'45'input2'45'to'45'output_2196
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
      C_load'45'indirect_2198
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1440 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1342
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2200
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1478 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1342
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2202 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2462
             (coe
                du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2204 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_792 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_store'45'indirect_2206
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1452 v0
                (coe
                   du_sv'45'as'45'loc_1342
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2208
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1490 v0
                (coe
                   du_sv'45'as'45'loc_1342
                   (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_lea'45'slot_2210 v4
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
      C_restore'45'input_2212 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2474
             (coe
                du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2214 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_660 (coe d_current'45'frame_648 (coe v3))
                (coe d_saved'45'frames_650 (coe v3))
                (coe d_frame'45'slots_652 (coe v3))
                (coe addInt (coe d_next'45'slot_654 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_656 (coe v3))
                (coe d_block'45'size_658 (coe v3)))
      C_instr'45'dealloc'45'stack_2216 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2218 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_660 (coe d_current'45'frame_648 (coe v3))
                (coe d_saved'45'frames_650 (coe v3))
                (coe d_frame'45'slots_652 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_656 (coe v3))
                (coe d_block'45'size_658 (coe v3)))
      C_instr'45'push'45'frame_2220 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2222
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2224
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2226 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2228 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_792 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4))
                (coe du_readReg_154 (coe d_regs_494 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_worklist'45'pop_2230 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2462
             (coe
                du_readLoc_712 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_648 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2232 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2238 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_502
                (coe
                   du_writeReg_168 (d_regs_494 (coe v2)) (coe C_Output_60)
                   (d_exec'45'sigop'45'output_2660
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_496 (coe v2)) (coe d_heapMem_498 (coe v2))
                (coe du_exec'45'sigop'45'halts_2676 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2242 v4 v5 v6
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
      C_instr'45'load'45'code'45'addr_2244 v4
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
      C_instr'45'save'45'closure'45'reg_2246
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2248 v4
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
      C_instr'45'case'45'on'45'tag_2250 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2772 (coe v0)
             (coe du_case'45'tag'45'at_2682 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2252 v4
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
      C_instr'45'loop_2254 v4
        -> coe
             d_exec'45'loop_2770 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2256 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_522 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2258 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2260 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1466
                (coe
                   du_slot'45'base_1462
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
d_exec'45'trace_2768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2188] ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2768 v0 v1 v2 v3
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
                       d_exec'45'trace_2768 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2766 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2766 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2188] ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2770 v0 v1 v2 v3 v4
  = coe
      du_exec'45'loop'45'run_2710
      (coe d_exec'45'trace_2768 (coe v0) (coe v2)) (coe v1) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_2772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  [T_AbstractInstr_2188] ->
  [T_AbstractInstr_2188] ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2772 v0 v1 v2 v3 v4 v5
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
                    0 -> coe d_exec'45'trace_2768 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2768 (coe v0) (coe v3) (coe v4) (coe v5)
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
d_exec'45'trace'45'cons_3062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2188 ->
  [T_AbstractInstr_2188] ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3062 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2188 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3108 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2188 -> ()) -> [T_AbstractInstr_2188] -> ()
d_AllI_3142 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_568 -> AgdaAny) ->
  (T_AbstractInstr_2188 -> ()) ->
  (T_AbstractInstr_2188 ->
   T_LocState_482 ->
   T_AllocState_568 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2188] ->
  AgdaAny ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3170 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_568 -> AgdaAny) ->
  (T_AbstractInstr_2188 -> ()) ->
  (T_AbstractInstr_2188 ->
   T_LocState_482 ->
   T_AllocState_568 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2188] ->
  [T_AbstractInstr_2188] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3260 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_482 -> T_AllocState_568 -> Integer -> Maybe Integer
d_getTag_3392 ~v0 v1 v2 v3 = du_getTag_3392 v1 v2 v3
du_getTag_3392 ::
  T_LocState_482 -> T_AllocState_568 -> Integer -> Maybe Integer
du_getTag_3392 v0 v1 v2
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
d_exec'45'tree'45'trace_3416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2264 ->
  T_LocState_482 ->
  T_AllocState_568 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3416 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2266
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2268 v4
        -> let v5 = d_halted_500 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2766 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2270 v4 v5
        -> let v6 = d_halted_500 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3416 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3416 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3416 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2272 v4 v5 v6
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
                                            d_exec'45'tree'45'trace_3416 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3416 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3416 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3416 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3416 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2274 v4
        -> let v5 = d_halted_500 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3416 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2276 v4
        -> coe d_exec'45'trace_2768 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3576 ::
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3576 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2264 ->
  T_TreeTrace_2264 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3594 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2188 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3640 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2264 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3680 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2188] ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3720 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2188] ->
  [T_AbstractInstr_2188] ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3740 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3798
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2264 ->
  T_LocState_482 ->
  T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3806 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3806
du_exec'45'tree'45'flat'45'equiv'45'simple_3806 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3806
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
