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
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Allocator.AbstractInstance
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
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
    C_SV'45'Code_80 Integer
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
  = C_mkRegs_154 T_StoredValue_68 T_StoredValue_68 T_StoredValue_68
                 Integer T_StoredValue_68 T_StoredValue_68
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_142 :: T_Registers_126 -> T_StoredValue_68
d_input1_142 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_144 :: T_Registers_126 -> T_StoredValue_68
d_input2_144 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_146 :: T_Registers_126 -> T_StoredValue_68
d_output_146 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_148 :: T_Registers_126 -> Integer
d_stackSlot_148 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.scratch
d_scratch_150 :: T_Registers_126 -> T_StoredValue_68
d_scratch_150 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.count
d_count_152 :: T_Registers_126 -> T_StoredValue_68
d_count_152 v0
  = case coe v0 of
      C_mkRegs_154 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 -> T_AbstractReg_54 -> T_StoredValue_68
d_readReg_158 ~v0 v1 v2 = du_readReg_158 v1 v2
du_readReg_158 ::
  T_Registers_126 -> T_AbstractReg_54 -> T_StoredValue_68
du_readReg_158 v0 v1
  = case coe v1 of
      C_Input1_56 -> coe d_input1_142 (coe v0)
      C_Input2_58 -> coe d_input2_144 (coe v0)
      C_Output_60 -> coe d_output_146 (coe v0)
      C_Scratch_62 -> coe d_scratch_150 (coe v0)
      C_Count_64 -> coe d_count_152 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 -> T_StoredValue_68 -> T_Registers_126
d_writeReg_172 ~v0 v1 v2 = du_writeReg_172 v1 v2
du_writeReg_172 ::
  T_Registers_126 ->
  T_AbstractReg_54 -> T_StoredValue_68 -> T_Registers_126
du_writeReg_172 v0 v1
  = case coe v1 of
      C_Input1_56
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe v2) (coe d_input2_144 (coe v0))
                  (coe d_output_146 (coe v0)) (coe d_stackSlot_148 (coe v0))
                  (coe d_scratch_150 (coe v0)) (coe d_count_152 (coe v0)))
      C_Input2_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe d_input1_142 (coe v0)) (coe v2)
                  (coe d_output_146 (coe v0)) (coe d_stackSlot_148 (coe v0))
                  (coe d_scratch_150 (coe v0)) (coe d_count_152 (coe v0)))
      C_Output_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe d_input1_142 (coe v0))
                  (coe d_input2_144 (coe v0)) (coe v2) (coe d_stackSlot_148 (coe v0))
                  (coe d_scratch_150 (coe v0)) (coe d_count_152 (coe v0)))
      C_Scratch_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe d_input1_142 (coe v0))
                  (coe d_input2_144 (coe v0)) (coe d_output_146 (coe v0))
                  (coe d_stackSlot_148 (coe v0)) (coe v2) (coe d_count_152 (coe v0)))
      C_Count_64
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_154 (coe d_input1_142 (coe v0))
                  (coe d_input2_144 (coe v0)) (coe d_output_146 (coe v0))
                  (coe d_stackSlot_148 (coe v0)) (coe d_scratch_150 (coe v0))
                  (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 -> Integer -> T_Registers_126
d_writeStackSlot_196 ~v0 v1 v2 = du_writeStackSlot_196 v1 v2
du_writeStackSlot_196 ::
  T_Registers_126 -> Integer -> T_Registers_126
du_writeStackSlot_196 v0 v1
  = coe
      C_mkRegs_154 (coe d_input1_142 (coe v0))
      (coe d_input2_144 (coe v0)) (coe d_output_146 (coe v0)) (coe v1)
      (coe d_scratch_150 (coe v0)) (coe d_count_152 (coe v0))
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 -> Integer -> T_Registers_126
d_incrStackSlot_204 ~v0 v1 v2 = du_incrStackSlot_204 v1 v2
du_incrStackSlot_204 ::
  T_Registers_126 -> Integer -> T_Registers_126
du_incrStackSlot_204 v0 v1
  = coe
      C_mkRegs_154 (coe d_input1_142 (coe v0))
      (coe d_input2_144 (coe v0)) (coe d_output_146 (coe v0))
      (coe addInt (coe d_stackSlot_148 (coe v0)) (coe v1))
      (coe d_scratch_150 (coe v0)) (coe d_count_152 (coe v0))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 -> Integer -> T_Registers_126
d_decrStackSlot_212 ~v0 v1 v2 = du_decrStackSlot_212 v1 v2
du_decrStackSlot_212 ::
  T_Registers_126 -> Integer -> T_Registers_126
du_decrStackSlot_212 v0 v1
  = coe
      C_mkRegs_154 (coe d_input1_142 (coe v0))
      (coe d_input2_144 (coe v0)) (coe d_output_146 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_148 (coe v0)) v1)
      (coe d_scratch_150 (coe v0)) (coe d_count_152 (coe v0))
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_232 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_412 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_442 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_474 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_506 = ()
data T_RegOp_506
  = C_scratch'45'one_508 | C_scratch'45'zero_510 |
    C_scratch'45'dec_512 | C_scratch'45'load'45'count_514 |
    C_count'45'zero_516 | C_count'45'inc_518
-- Once.CCC.Machine.SMCore.sv-succ
d_sv'45'succ_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 -> T_StoredValue_68
d_sv'45'succ_522 ~v0 v1 = du_sv'45'succ_522 v1
du_sv'45'succ_522 :: T_StoredValue_68 -> T_StoredValue_68
du_sv'45'succ_522 v0
  = let v1 = coe C_SV'45'Tag_74 (coe (1 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_74 v2
           -> coe C_SV'45'Tag_74 (coe addInt (coe (1 :: Integer)) (coe v2))
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-pred
d_sv'45'pred_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 -> T_StoredValue_68
d_sv'45'pred_528 ~v0 v1 = du_sv'45'pred_528 v1
du_sv'45'pred_528 :: T_StoredValue_68 -> T_StoredValue_68
du_sv'45'pred_528 v0
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
d_sv'45'tag'45'val_534 :: T_StoredValue_68 -> Integer
d_sv'45'tag'45'val_534 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_SV'45'Tag_74 v2 -> coe v2
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.LocState
d_LocState_540 a0 = ()
data T_LocState_540
  = C_mkLocState_560 T_Registers_126
                     (AgdaAny -> Integer -> Maybe T_StoredValue_68)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_68)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_552 :: T_LocState_540 -> T_Registers_126
d_regs_552 v0
  = case coe v0 of
      C_mkLocState_560 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_554 ::
  T_LocState_540 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_stackMem_554 v0
  = case coe v0 of
      C_mkLocState_560 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_556 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_heapMem_556 v0
  = case coe v0 of
      C_mkLocState_560 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_558 :: T_LocState_540 -> Bool
d_halted_558 v0
  = case coe v0 of
      C_mkLocState_560 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_506 -> T_Registers_126 -> T_Registers_126
d_setReg_564 ~v0 v1 v2 = du_setReg_564 v1 v2
du_setReg_564 :: T_RegOp_506 -> T_Registers_126 -> T_Registers_126
du_setReg_564 v0 v1
  = case coe v0 of
      C_scratch'45'one_508
        -> coe
             du_writeReg_172 v1 (coe C_Scratch_62)
             (coe C_SV'45'Tag_74 (coe (1 :: Integer)))
      C_scratch'45'zero_510
        -> coe
             du_writeReg_172 v1 (coe C_Scratch_62)
             (coe C_SV'45'Tag_74 (coe (0 :: Integer)))
      C_scratch'45'dec_512
        -> coe
             du_writeReg_172 v1 (coe C_Scratch_62)
             (coe
                du_sv'45'pred_528 (coe du_readReg_158 (coe v1) (coe C_Scratch_62)))
      C_scratch'45'load'45'count_514
        -> coe
             du_writeReg_172 v1 (coe C_Scratch_62)
             (coe du_readReg_158 (coe v1) (coe C_Count_64))
      C_count'45'zero_516
        -> coe
             du_writeReg_172 v1 (coe C_Count_64)
             (coe C_SV'45'Tag_74 (coe (0 :: Integer)))
      C_count'45'inc_518
        -> coe
             du_writeReg_172 v1 (coe C_Count_64)
             (coe
                du_sv'45'succ_522 (coe du_readReg_158 (coe v1) (coe C_Count_64)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_506 -> T_LocState_540 -> T_LocState_540
d_exec'45'reg'45'op_580 ~v0 v1 v2 = du_exec'45'reg'45'op_580 v1 v2
du_exec'45'reg'45'op_580 ::
  T_RegOp_506 -> T_LocState_540 -> T_LocState_540
du_exec'45'reg'45'op_580 v0 v1
  = coe
      C_mkLocState_560
      (coe du_setReg_564 (coe v0) (coe d_regs_552 (coe v1)))
      (coe d_stackMem_554 (coe v1)) (coe d_heapMem_556 (coe v1))
      (coe d_halted_558 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_586 = ()
data T_AllocMode_586 = C_Stack_588 | C_Heap_590
-- Once.CCC.Machine.SMCore.size-with-aux
d_size'45'with'45'aux_598 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_size'45'with'45'aux_598 v0 v1 ~v2 v3 v4
  = du_size'45'with'45'aux_598 v0 v1 v3 v4
du_size'45'with'45'aux_598 ::
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_size'45'with'45'aux_598 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe v0)
             else coe seq (coe v5) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.size-with
d_size'45'with_614 ::
  Integer -> Integer -> (Integer -> Integer) -> Integer -> Integer
d_size'45'with_614 v0 v1 v2 v3
  = coe
      du_size'45'with'45'aux_598 (coe v0) (coe v3) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v1))
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_626 a0 = ()
data T_AllocState_626
  = C_mkAllocState_714 AgdaAny [AgdaAny] Integer Integer
                       (Integer -> Integer)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_704 :: T_AllocState_626 -> AgdaAny
d_current'45'frame_704 v0
  = case coe v0 of
      C_mkAllocState_714 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_706 :: T_AllocState_626 -> [AgdaAny]
d_saved'45'frames_706 v0
  = case coe v0 of
      C_mkAllocState_714 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_708 :: T_AllocState_626 -> Integer
d_next'45'slot_708 v0
  = case coe v0 of
      C_mkAllocState_714 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_710 :: T_AllocState_626 -> Integer
d_next'45'heap'45'ref_710 v0
  = case coe v0 of
      C_mkAllocState_714 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_712 :: T_AllocState_626 -> Integer -> Integer
d_block'45'size_712 v0
  = case coe v0 of
      C_mkAllocState_714 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_752 ::
  T_LocState_540 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_752 v0 v1 v2 = coe d_stackMem_554 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_760 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_760 v0 v1 = coe d_heapMem_556 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_766 ~v0 v1 v2 = du_readLoc_766 v1 v2
du_readLoc_766 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_766 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_554 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_556 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_786 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_786 v5 v6 v7 v8
du_writeStackMem'45'aux_786 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_786 v0 v1 v2 v3
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
d_writeStackMem_794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_794 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_786
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_812 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_812 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_812 v3 v4 v5
du_writeHeapMem'45'aux_812 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_812 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_818 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_818 v1 v2 v3 v4
du_writeHeapMem_818 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_818 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_812
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_540
d_writeLocToStack_828 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_560 (coe d_regs_552 (coe v1))
      (coe
         d_writeStackMem_794 (coe v0) (coe d_stackMem_554 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_556 (coe v1)) (coe d_halted_558 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLocToHeap_838 ~v0 v1 v2 v3 = du_writeLocToHeap_838 v1 v2 v3
du_writeLocToHeap_838 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
du_writeLocToHeap_838 v0 v1 v2
  = coe
      C_mkLocState_560 (coe d_regs_552 (coe v0))
      (coe d_stackMem_554 (coe v0))
      (coe
         du_writeHeapMem_818 (coe d_heapMem_556 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_558 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLoc_846 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_828 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_72 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_838 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_74 v5
               -> coe du_writeLocToHeap_838 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_78 v5 v6 v7
               -> coe du_writeLocToHeap_838 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_80 v5
               -> coe du_writeLocToHeap_838 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_896 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_934 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_974 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_974 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_994 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_994 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1022 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1054 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1332 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1384 a0 = ()
data T_LocSourceExt_1384
  = C_Loc_1388 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1390 T_AbstractReg_54 | C_IndRegSuc_1392 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1396 ~v0 v1 = du_sv'45'as'45'loc_1396 v1
du_sv'45'as'45'loc_1396 ::
  T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1396 v0
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
d_resolveSourceExt_1402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_126 ->
  T_LocSourceExt_1384 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1402 ~v0 v1 v2 = du_resolveSourceExt_1402 v1 v2
du_resolveSourceExt_1402 ::
  T_Registers_126 ->
  T_LocSourceExt_1384 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1402 v0 v1
  = case coe v1 of
      C_Loc_1388 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1390 v2
        -> coe
             du_sv'45'as'45'loc_1396 (coe du_readReg_158 (coe v0) (coe v2))
      C_IndRegSuc_1392 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1396 (coe du_readReg_158 (coe v0) (coe v2)) in
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
d_Instr_1432 a0 = ()
data T_Instr_1432
  = C_load_1436 T_AbstractReg_54 T_LocSourceExt_1384 |
    C_store_1438 T_LocSourceExt_1384 T_AbstractReg_54 |
    C_mov_1440 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1448 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_1448 v0 v1 = coe d_heapMem_556 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_1450 ~v0 = du_readLoc_1450
du_readLoc_1450 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_1450 = coe du_readLoc_766
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1452 ::
  T_LocState_540 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_1452 v0 v1 v2 = coe d_stackMem_554 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_1454 ~v0 = du_writeHeapMem_1454
du_writeHeapMem_1454 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_1454 = coe du_writeHeapMem_818
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_1456 ~v0 = du_writeHeapMem'45'aux_1456
du_writeHeapMem'45'aux_1456 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_1456 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_812 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLoc_1458 v0 = coe d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1460 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1462 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1462 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1464 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1466 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1468 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1470 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1472 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1472 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLocToHeap_1474 ~v0 = du_writeLocToHeap_1474
du_writeLocToHeap_1474 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
du_writeLocToHeap_1474 = coe du_writeLocToHeap_838
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_540
d_writeLocToStack_1476 v0 = coe d_writeLocToStack_828 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_1478 v0 = coe d_writeStackMem_794 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_1480 ~v0 = du_writeStackMem'45'aux_1480
du_writeStackMem'45'aux_1480 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_1480 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_786 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'load'45'with'45'value_1482 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1482 v1 v2
du_exec'45'load'45'with'45'value_1482 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
du_exec'45'load'45'with'45'value_1482 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_560 (coe du_writeReg_172 (d_regs_552 (coe v3)) v0 v2)
                  (coe d_stackMem_554 (coe v3)) (coe d_heapMem_556 (coe v3))
                  (coe d_halted_558 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_560 (coe d_regs_552 (coe v2))
                  (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
d_exec'45'load'45'via'45'resolved_1494 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1494 v1 v2
du_exec'45'load'45'via'45'resolved_1494 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
du_exec'45'load'45'via'45'resolved_1494 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1482 v0
                  (coe du_readLoc_766 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_560 (coe d_regs_552 (coe v2))
                  (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'store'45'via'45'resolved_1506 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_846 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_560 (coe d_regs_552 (coe v3))
                  (coe d_stackMem_554 (coe v3)) (coe d_heapMem_556 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1516 ~v0 v1 = du_slot'45'base_1516 v1
du_slot'45'base_1516 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1516 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1396 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_540 -> T_LocState_540
d_exec'45'lea'45'indexed'45'via_1520 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1520 v1
du_exec'45'lea'45'indexed'45'via_1520 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_540 -> T_LocState_540
du_exec'45'lea'45'indexed'45'via_1520 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_560
                  (coe
                     du_writeReg_172 (d_regs_552 (coe v3)) (coe C_Input1_56)
                     (coe C_SV'45'Ptr_72 (coe du_offsetLoc_94 (coe v1) (coe v2))))
                  (coe d_stackMem_554 (coe v3)) (coe d_heapMem_556 (coe v3))
                  (coe d_halted_558 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_560 (coe d_regs_552 (coe v2))
                  (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
d_exec'45'load'45'suc'45'via'45'resolved_1532 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1532 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1532 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
du_exec'45'load'45'suc'45'via'45'resolved_1532 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1482 v0
                  (coe du_readLoc_766 (coe v3) (coe du_sucLoc_84 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_560 (coe d_regs_552 (coe v2))
                  (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1544 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'store'45'suc'45'via'45'resolved_1544 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_846
                  (coe v0) (coe v4) (coe du_sucLoc_84 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_560 (coe d_regs_552 (coe v3))
                  (coe d_stackMem_554 (coe v3)) (coe d_heapMem_556 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1432 -> T_LocState_540 -> T_LocState_540
d_exec_1554 v0 v1
  = case coe v1 of
      C_load_1436 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1494 v2
                  (coe du_resolveSourceExt_1402 (coe d_regs_552 (coe v4)) (coe v3))
                  v4)
      C_store_1438 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1506 v0
                  (coe du_resolveSourceExt_1402 (coe d_regs_552 (coe v4)) (coe v2))
                  (coe du_readReg_158 (coe d_regs_552 (coe v4)) (coe v3)) v4)
      C_mov_1440 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_560
                  (coe
                     du_writeReg_172 (d_regs_552 (coe v4)) v2
                     (coe du_readReg_158 (coe d_regs_552 (coe v4)) (coe v3)))
                  (coe d_stackMem_554 (coe v4)) (coe d_heapMem_556 (coe v4))
                  (coe d_halted_558 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1580 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1586 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1432] -> T_LocState_540 -> T_LocState_540
d_execList_1588 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_558 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1588 (coe v0) (coe v4) (coe d_exec_1554 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1620 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_1620 v0 v1 = coe d_heapMem_556 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_1622 ~v0 = du_readLoc_1622
du_readLoc_1622 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_1622 = coe du_readLoc_766
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1624 ::
  T_LocState_540 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_1624 v0 v1 v2 = coe d_stackMem_554 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_1626 ~v0 = du_writeHeapMem_1626
du_writeHeapMem_1626 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_1626 = coe du_writeHeapMem_818
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_1628 ~v0 = du_writeHeapMem'45'aux_1628
du_writeHeapMem'45'aux_1628 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_1628 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_812 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLoc_1630 v0 = coe d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1632 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1634 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1634 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1636 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1638 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1640 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1642 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1644 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1644 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLocToHeap_1646 ~v0 = du_writeLocToHeap_1646
du_writeLocToHeap_1646 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
du_writeLocToHeap_1646 = coe du_writeLocToHeap_838
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_540
d_writeLocToStack_1648 v0 = coe d_writeLocToStack_828 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_1650 v0 = coe d_writeStackMem_794 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_1652 ~v0 = du_writeStackMem'45'aux_1652
du_writeStackMem'45'aux_1652 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_1652 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_786 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1432 -> T_LocState_540 -> T_LocState_540
d_exec_1656 v0 = coe d_exec_1554 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_540 -> T_LocState_540
d_exec'45'lea'45'indexed'45'via_1658 ~v0
  = du_exec'45'lea'45'indexed'45'via_1658
du_exec'45'lea'45'indexed'45'via_1658 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_540 -> T_LocState_540
du_exec'45'lea'45'indexed'45'via_1658
  = coe du_exec'45'lea'45'indexed'45'via_1520
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1660 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1662 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
d_exec'45'load'45'suc'45'via'45'resolved_1664 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1664
du_exec'45'load'45'suc'45'via'45'resolved_1664 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
du_exec'45'load'45'suc'45'via'45'resolved_1664
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1532
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
d_exec'45'load'45'via'45'resolved_1666 ~v0
  = du_exec'45'load'45'via'45'resolved_1666
du_exec'45'load'45'via'45'resolved_1666 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
du_exec'45'load'45'via'45'resolved_1666
  = coe du_exec'45'load'45'via'45'resolved_1494
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'load'45'with'45'value_1668 ~v0
  = du_exec'45'load'45'with'45'value_1668
du_exec'45'load'45'with'45'value_1668 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
du_exec'45'load'45'with'45'value_1668
  = coe du_exec'45'load'45'with'45'value_1482
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'store'45'suc'45'via'45'resolved_1670 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1544 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'store'45'via'45'resolved_1672 v0
  = coe d_exec'45'store'45'via'45'resolved_1506 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1432] -> T_LocState_540 -> T_LocState_540
d_execList_1674 v0 = coe d_execList_1588 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1676 ~v0 = du_slot'45'base_1676
du_slot'45'base_1676 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1676 = coe du_slot'45'base_1516
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 -> T_LocSourceExt_1384 -> Maybe T_StoredValue_68
d_resolved'45'readLoc_1678 ~v0 v1 v2
  = du_resolved'45'readLoc_1678 v1 v2
du_resolved'45'readLoc_1678 ::
  T_LocState_540 -> T_LocSourceExt_1384 -> Maybe T_StoredValue_68
du_resolved'45'readLoc_1678 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1402 (coe d_regs_552 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_766 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1708 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1778 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1854 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1884 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1940 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1992 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2044 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2044 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2060 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2078 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2092 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2092 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2110 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2176 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2200 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2228 = ()
data T_FlatCtrl_2228
  = C_c'45'label_2230 Integer | C_c'45'jmp_2232 Integer |
    C_c'45'branch'45'scratch'45'zero_2234 Integer |
    C_c'45'branch'45'tag'45'zero_2236 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2238 = ()
data T_AbstractInstr_2238
  = C_mov'45'to'45'output_2240 | C_mov'45'to'45'input_2242 |
    C_mov'45'output'45'to'45'input2_2244 |
    C_mov'45'input2'45'to'45'output_2246 | C_load'45'indirect_2248 |
    C_load'45'indirect'45'suc_2250 |
    C_load'45'from'45'slot_2252 Integer |
    C_store'45'at'45'slot_2254 Integer | C_store'45'indirect_2256 |
    C_store'45'indirect'45'suc_2258 | C_lea'45'slot_2260 Integer |
    C_restore'45'input_2262 Integer |
    C_instr'45'alloc'45'stack_2264 Integer |
    C_instr'45'dealloc'45'stack_2266 Integer |
    C_instr'45'reclaim'45'to_2268 Integer |
    C_instr'45'push'45'frame_2270 Integer |
    C_instr'45'pop'45'frame_2272 | C_instr'45'call'45'closure_2274 |
    C_worklist'45'init_2276 Integer | C_worklist'45'push_2278 Integer |
    C_worklist'45'pop_2280 Integer | C_worklist'45'check_2282 Integer |
    C_instr'45'sigop_2288 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 |
    C_instr'45'load'45'const_2292 MAlonzo.Code.Once.Type.T_Type_112
                                  MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_instr'45'load'45'code'45'addr_2294 Integer |
    C_instr'45'save'45'closure'45'reg_2296 |
    C_instr'45'load'45'tag'45'lit_2298 Integer |
    C_instr'45'case'45'on'45'tag_2300 [T_AbstractInstr_2238]
                                      [T_AbstractInstr_2238] |
    C_instr'45'alloc'45'heap_2302 Integer |
    C_instr'45'loop_2304 [T_AbstractInstr_2238] |
    C_instr'45'reg'45'op_2306 T_RegOp_506 |
    C_instr'45'ctrl_2308 T_FlatCtrl_2228 |
    C_lea'45'indexed_2310 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2312 :: ()
d_AbstractTrace_2312 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2314 = ()
data T_TreeTrace_2314
  = C_ε_2316 | C_instr_2318 T_AbstractInstr_2238 |
    C__'9656'__2320 T_TreeTrace_2314 T_TreeTrace_2314 |
    C_branch_2322 Integer T_TreeTrace_2314 T_TreeTrace_2314 |
    C_call'45'sub_2324 T_TreeTrace_2314 |
    C_flat_2326 [T_AbstractInstr_2238]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2328 :: [T_AbstractInstr_2238] -> T_TreeTrace_2314
d_flatToTree_2328 v0
  = case coe v0 of
      [] -> coe C_ε_2316
      (:) v1 v2
        -> coe
             C__'9656'__2320 (coe C_instr_2318 (coe v1))
             (coe d_flatToTree_2328 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2334 :: T_TreeTrace_2314 -> [T_AbstractInstr_2238]
d_treeToFlat_2334 v0
  = case coe v0 of
      C_ε_2316 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2318 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2320 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2334 (coe v1)) (coe d_treeToFlat_2334 (coe v2))
      C_branch_2322 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2334 (coe v2)) (coe d_treeToFlat_2334 (coe v3))
      C_call'45'sub_2324 v1 -> coe d_treeToFlat_2334 (coe v1)
      C_flat_2326 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2350 ::
  Integer -> T_TreeTrace_2314 -> [T_AbstractInstr_2238]
d_treeToRunnable_2350 v0 v1
  = case coe v1 of
      C_ε_2316 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2318 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2320 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2350 (coe v0) (coe v2))
             (coe d_treeToRunnable_2350 (coe v0) (coe v3))
      C_branch_2322 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2350 (coe v0) (coe v3))
             (coe d_treeToRunnable_2350 (coe v0) (coe v4))
      C_call'45'sub_2324 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2278 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2350 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2280 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2326 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2380 ::
  Integer -> T_TreeTrace_2314 -> [T_AbstractInstr_2238]
d_treeToRunnableWithInit_2380 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2276 (coe v0))
      (coe d_treeToRunnable_2350 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2424 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_readHeapLoc_2424 v0 v1 = coe d_heapMem_556 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
d_readLoc_2426 ~v0 = du_readLoc_2426
du_readLoc_2426 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_68
du_readLoc_2426 = coe du_readLoc_766
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2428 ::
  T_LocState_540 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_readStackLoc_2428 v0 v1 v2 = coe d_stackMem_554 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
d_writeHeapMem_2430 ~v0 = du_writeHeapMem_2430
du_writeHeapMem_2430 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_68
du_writeHeapMem_2430 = coe du_writeHeapMem_818
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeHeapMem'45'aux_2432 ~v0 = du_writeHeapMem'45'aux_2432
du_writeHeapMem'45'aux_2432 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeHeapMem'45'aux_2432 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_812 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLoc_2434 v0 = coe d_writeLoc_846 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2436 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2438 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2438 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2440 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2442 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2444 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2446 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2448 ::
  T_LocState_540 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 ->
  T_Registers_126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2448 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
d_writeLocToHeap_2450 ~v0 = du_writeLocToHeap_2450
du_writeLocToHeap_2450 ::
  T_LocState_540 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_68 -> T_LocState_540
du_writeLocToHeap_2450 = coe du_writeLocToHeap_838
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  AgdaAny -> Integer -> T_StoredValue_68 -> T_LocState_540
d_writeLocToStack_2452 v0 = coe d_writeLocToStack_828 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_68 -> AgdaAny -> Integer -> Maybe T_StoredValue_68
d_writeStackMem_2454 v0 = coe d_writeStackMem_794 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
d_writeStackMem'45'aux_2456 ~v0 = du_writeStackMem'45'aux_2456
du_writeStackMem'45'aux_2456 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_68 ->
  T_StoredValue_68 -> Maybe T_StoredValue_68
du_writeStackMem'45'aux_2456 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_786 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1432 -> T_LocState_540 -> T_LocState_540
d_exec_2460 v0 = coe d_exec_1554 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_540 -> T_LocState_540
d_exec'45'lea'45'indexed'45'via_2462 ~v0
  = du_exec'45'lea'45'indexed'45'via_2462
du_exec'45'lea'45'indexed'45'via_2462 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_540 -> T_LocState_540
du_exec'45'lea'45'indexed'45'via_2462
  = coe du_exec'45'lea'45'indexed'45'via_1520
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2464 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2466 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
d_exec'45'load'45'suc'45'via'45'resolved_2468 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2468
du_exec'45'load'45'suc'45'via'45'resolved_2468 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
du_exec'45'load'45'suc'45'via'45'resolved_2468
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1532
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
d_exec'45'load'45'via'45'resolved_2470 ~v0
  = du_exec'45'load'45'via'45'resolved_2470
du_exec'45'load'45'via'45'resolved_2470 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> T_LocState_540
du_exec'45'load'45'via'45'resolved_2470
  = coe du_exec'45'load'45'via'45'resolved_1494
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'load'45'with'45'value_2472 ~v0
  = du_exec'45'load'45'with'45'value_2472
du_exec'45'load'45'with'45'value_2472 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
du_exec'45'load'45'with'45'value_2472
  = coe du_exec'45'load'45'with'45'value_1482
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'store'45'suc'45'via'45'resolved_2474 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1544 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68 -> T_LocState_540 -> T_LocState_540
d_exec'45'store'45'via'45'resolved_2476 v0
  = coe d_exec'45'store'45'via'45'resolved_1506 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1432] -> T_LocState_540 -> T_LocState_540
d_execList_2478 v0 = coe d_execList_1588 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2480 ~v0 = du_slot'45'base_2480
du_slot'45'base_2480 ::
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2480 = coe du_slot'45'base_1516
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2484 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  T_LocState_540 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2486 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2488 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2490 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2492 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_AbstractReg_54 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2494 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2496 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1384 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 ->
  T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2498 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2500 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2502 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2504 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_540 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2506 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 ->
  T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2508 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 -> T_LocSourceExt_1384 -> Maybe T_StoredValue_68
d_resolved'45'readLoc_2510 ~v0 = du_resolved'45'readLoc_2510
du_resolved'45'readLoc_2510 ::
  T_LocState_540 -> T_LocSourceExt_1384 -> Maybe T_StoredValue_68
du_resolved'45'readLoc_2510 = coe du_resolved'45'readLoc_1678
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2512 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2512 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2512 ::
  Maybe T_StoredValue_68 ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2512 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe du_writeReg_172 (d_regs_552 (coe v1)) (coe C_Output_60) v3)
                (coe d_stackMem_554 (coe v1)) (coe d_heapMem_556 (coe v1))
                (coe d_halted_558 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560 (coe d_regs_552 (coe v1))
                (coe d_stackMem_554 (coe v1)) (coe d_heapMem_556 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2524 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2524 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2524 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2524 ::
  Maybe T_StoredValue_68 ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2524 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe du_writeReg_172 (d_regs_552 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_554 (coe v1)) (coe d_heapMem_556 (coe v1))
                (coe d_halted_558 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560 (coe d_regs_552 (coe v1))
                (coe d_stackMem_554 (coe v1)) (coe d_heapMem_556 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2542 ::
  T_StoredValue_68 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2542 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2548 ::
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2548 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2556 ::
  T_StoredValue_68 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2556 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2562 ::
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2562 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_68
d_unit'45'storedvalue_2564 ~v0 = du_unit'45'storedvalue_2564
du_unit'45'storedvalue_2564 :: T_StoredValue_68
du_unit'45'storedvalue_2564
  = coe
      C_SV'45'Lit_78 (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2570 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2570 v3 v4
du_combine'45'typed_2570 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2570 v0 v1
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
d_readTyped'45'int_2576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 -> Maybe Integer
d_readTyped'45'int_2576 ~v0 v1 = du_readTyped'45'int_2576 v1
du_readTyped'45'int_2576 :: Maybe T_StoredValue_68 -> Maybe Integer
du_readTyped'45'int_2576 v0
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
d_readTyped'45'pair_2584 ::
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
d_readTyped'45'pair_2584 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'pair_2584 v3 v4 v5 v6
du_readTyped'45'pair_2584 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_68 ->
  Maybe T_StoredValue_68 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2584 v0 v1 v2 v3
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
                                -> coe du_combine'45'typed_2570 (coe v0 v6) (coe v1 v8)
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_68 -> Maybe AgdaAny
d_readReg'45'typed_2600 ~v0 v1 v2 = du_readReg'45'typed_2600 v1 v2
du_readReg'45'typed_2600 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_68 -> Maybe AgdaAny
du_readReg'45'typed_2600 v0 v1
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
d_readTyped_2606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> Maybe AgdaAny
d_readTyped_2606 ~v0 v1 v2 v3 = du_readTyped_2606 v1 v2 v3
du_readTyped_2606 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_540 -> Maybe AgdaAny
du_readTyped_2606 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
           -> coe
                du_readTyped'45'pair_2584
                (coe (\ v6 -> coe du_readTyped_2606 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2606 (coe v5) (coe v6) (coe v2)))
                (coe du_readLoc_766 (coe v2) (coe v1))
                (coe du_readLoc_766 (coe v2) (coe du_sucLoc_84 (coe v1)))
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe
                du_readTyped'45'int_2576 (coe du_readLoc_766 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2636
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_540 -> T_StoredValue_68
d_pure'45'sigop'45'output_2642 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_2664 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v2))
      (coe
         du_sv'45'as'45'loc_1396
         (coe du_readReg_158 (coe d_regs_552 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_68
d_pure'45'sigop'45'out'45'val_2648 ~v0 ~v1 v2 v3 v4 v5
  = du_pure'45'sigop'45'out'45'val_2648 v2 v3 v4 v5
du_pure'45'sigop'45'out'45'val_2648 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_68
du_pure'45'sigop'45'out'45'val_2648 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_SV'45'Lit_78 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.SigOp.Info.du_semM_188 v1 v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2564
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_540 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_68
d_pure'45'sigop'45'out'45'aux_2664 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pure'45'sigop'45'out'45'val_2648 (coe v2) (coe v3) (coe v7)
                    (coe du_readTyped_2606 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'sigop'45'out'45'val_2648 (coe v2) (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2600 (coe v1)
                       (coe du_readReg_158 (coe d_regs_552 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2636 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_540 -> T_StoredValue_68
d_exec'45'sigop'45'output'45'of_2700 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_pure'45'sigop'45'output_2642 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe du_unit'45'storedvalue_2564
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe du_unit'45'storedvalue_2564
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_540 -> T_StoredValue_68
d_exec'45'sigop'45'output_2710 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2700 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_540 -> Bool
d_exec'45'sigop'45'halts'45'of_2720 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2720 v3
du_exec'45'sigop'45'halts'45'of_2720 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> Bool
du_exec'45'sigop'45'halts'45'of_2720 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_540 -> Bool
d_exec'45'sigop'45'halts_2726 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2726 v3
du_exec'45'sigop'45'halts_2726 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 -> Bool
du_exec'45'sigop'45'halts_2726 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2720
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2732 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 -> Maybe T_StoredValue_68
d_case'45'tag'45'at_2732 ~v0 v1 = du_case'45'tag'45'at_2732 v1
du_case'45'tag'45'at_2732 ::
  T_LocState_540 -> Maybe T_StoredValue_68
du_case'45'tag'45'at_2732 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1396
              (coe d_input1_142 (coe d_regs_552 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_766 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.BodyRunner
d_BodyRunner_2746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_2746 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_2748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 -> T_LocState_540 -> T_LocState_540
d_loop'45'reanchor'45'loc_2748 ~v0 v1 v2
  = du_loop'45'reanchor'45'loc_2748 v1 v2
du_loop'45'reanchor'45'loc_2748 ::
  T_LocState_540 -> T_LocState_540 -> T_LocState_540
du_loop'45'reanchor'45'loc_2748 v0 v1
  = coe
      C_mkLocState_560 (coe d_regs_552 (coe v1))
      (coe d_stackMem_554 (coe v0)) (coe d_heapMem_556 (coe v1))
      (coe d_halted_558 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_2754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_626 -> T_AllocState_626 -> T_AllocState_626
d_loop'45'reanchor'45'alloc_2754 ~v0 v1 v2
  = du_loop'45'reanchor'45'alloc_2754 v1 v2
du_loop'45'reanchor'45'alloc_2754 ::
  T_AllocState_626 -> T_AllocState_626 -> T_AllocState_626
du_loop'45'reanchor'45'alloc_2754 v0 v1
  = coe
      C_mkAllocState_714 (coe d_current'45'frame_704 (coe v0))
      (coe d_saved'45'frames_706 (coe v1))
      (coe d_next'45'slot_708 (coe v0))
      (coe d_next'45'heap'45'ref_710 (coe v1))
      (coe d_block'45'size_712 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_2760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_540 ->
   T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_2760 ~v0 v1 v2 v3 v4
  = du_exec'45'loop'45'run_2760 v1 v2 v3 v4
du_exec'45'loop'45'run_2760 ::
  (T_LocState_540 ->
   T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_2760 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560 (coe d_regs_552 (coe v2))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_558 (coe v2) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                   else (let v6 = d_scratch_150 (coe d_regs_552 (coe v2)) in
                         coe
                           (let v7
                                  = coe
                                      du_exec'45'loop'45'run_2760 (coe v0) (coe v4)
                                      (coe
                                         du_loop'45'reanchor'45'loc_2748 (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe v0 v2 v3)))
                                      (coe
                                         du_loop'45'reanchor'45'alloc_2754 (coe v3)
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
d_exec'45'abstract_2816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2816 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2240
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2242
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Output_60)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_2244
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Input2_58)
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Output_60)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_2246
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Input2_58)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_load'45'indirect_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1494 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1396
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2250
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1532 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1396
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2252 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2512
             (coe
                du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_704 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2254 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_846 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_704 (coe v3)) (coe v4))
                (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_store'45'indirect_2256
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1506 v0
                (coe
                   du_sv'45'as'45'loc_1396
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2258
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1544 v0
                (coe
                   du_sv'45'as'45'loc_1396
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_lea'45'slot_2260 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe
                      C_SV'45'Ptr_72
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_704 (coe v3)) (coe v4))))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_restore'45'input_2262 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2524
             (coe
                du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_704 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2264 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe du_incrStackSlot_204 (coe d_regs_552 (coe v2)) (coe v4))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe
                C_mkAllocState_714 (coe d_current'45'frame_704 (coe v3))
                (coe d_saved'45'frames_706 (coe v3))
                (coe addInt (coe d_next'45'slot_708 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_710 (coe v3))
                (coe d_block'45'size_712 (coe v3)))
      C_instr'45'dealloc'45'stack_2266 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe du_decrStackSlot_212 (coe d_regs_552 (coe v2)) (coe v4))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_2268 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_714 (coe d_current'45'frame_704 (coe v3))
                (coe d_saved'45'frames_706 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_710 (coe v3))
                (coe d_block'45'size_712 (coe v3)))
      C_instr'45'push'45'frame_2270 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeStackSlot_196 (coe d_regs_552 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_2272
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2274
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2276 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2278 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_846 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_704 (coe v3)) (coe v4))
                (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_worklist'45'pop_2280 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2512
             (coe
                du_readLoc_766 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_704 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2282 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2288 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (d_exec'45'sigop'45'output_2710
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe du_exec'45'sigop'45'halts_2726 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2292 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Lit_78 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2294 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Code_80 (coe v4)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2296
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2298 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Tag_74 (coe v4)))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2300 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2822 (coe v0)
             (coe du_case'45'tag'45'at_2732 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2302 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560
                (coe
                   du_writeReg_172 (d_regs_552 (coe v2)) (coe C_Output_60)
                   (coe
                      C_SV'45'Ptr_72
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_710 (coe v3)))))))
                (coe d_stackMem_554 (coe v2)) (coe d_heapMem_556 (coe v2))
                (coe d_halted_558 (coe v2)))
             (coe
                C_mkAllocState_714 (coe d_current'45'frame_704 (coe v3))
                (coe d_saved'45'frames_706 (coe v3))
                (coe d_next'45'slot_708 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_710 (coe v3)))))
                (coe
                   d_size'45'with_614 (coe v4)
                   (coe d_next'45'heap'45'ref_710 (coe v3))
                   (coe d_block'45'size_712 (coe v3))))
      C_instr'45'loop_2304 v4
        -> coe
             d_exec'45'loop_2820 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2306 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_580 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2308 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2310 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1520
                (coe
                   du_slot'45'base_1516
                   (coe
                      du_readLoc_766 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_704 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_534
                   (coe du_readReg_158 (coe d_regs_552 (coe v2)) (coe C_Scratch_62)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2238] ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2818 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_558 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2818 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2816 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2816 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2238] ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2820 v0 v1 v2 v3 v4
  = coe
      du_exec'45'loop'45'run_2760
      (coe d_exec'45'trace_2818 (coe v0) (coe v2)) (coe v1) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_2822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_68 ->
  [T_AbstractInstr_2238] ->
  [T_AbstractInstr_2238] ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2822 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_72 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_560 (coe d_regs_552 (coe v4))
                       (coe d_stackMem_554 (coe v4)) (coe d_heapMem_556 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Tag_74 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_2818 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2818 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_78 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_560 (coe d_regs_552 (coe v4))
                       (coe d_stackMem_554 (coe v4)) (coe d_heapMem_556 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Code_80 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_560 (coe d_regs_552 (coe v4))
                       (coe d_stackMem_554 (coe v4)) (coe d_heapMem_556 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_560 (coe d_regs_552 (coe v4))
                (coe d_stackMem_554 (coe v4)) (coe d_heapMem_556 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_3112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  [T_AbstractInstr_2238] ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3112 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3158 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2238 -> ()) -> [T_AbstractInstr_2238] -> ()
d_AllI_3192 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_626 -> AgdaAny) ->
  (T_AbstractInstr_2238 -> ()) ->
  (T_AbstractInstr_2238 ->
   T_LocState_540 ->
   T_AllocState_626 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2238] ->
  AgdaAny ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3220 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_626 -> AgdaAny) ->
  (T_AbstractInstr_2238 -> ()) ->
  (T_AbstractInstr_2238 ->
   T_LocState_540 ->
   T_AllocState_626 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2238] ->
  [T_AbstractInstr_2238] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3310 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_540 -> T_AllocState_626 -> Integer -> Maybe Integer
d_getTag_3442 ~v0 v1 v2 v3 = du_getTag_3442 v1 v2 v3
du_getTag_3442 ::
  T_LocState_540 -> T_AllocState_626 -> Integer -> Maybe Integer
du_getTag_3442 v0 v1 v2
  = let v3
          = coe d_stackMem_554 v0 (d_current'45'frame_704 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2314 ->
  T_LocState_540 ->
  T_AllocState_626 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3466 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2316
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2318 v4
        -> let v5 = d_halted_558 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2816 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2320 v4 v5
        -> let v6 = d_halted_558 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3466 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3466 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3466 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2322 v4 v5 v6
        -> let v7 = d_halted_558 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_554 v2 (d_current'45'frame_704 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3466 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3466 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3466 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3466 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3466 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2324 v4
        -> let v5 = d_halted_558 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3466 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2326 v4
        -> coe d_exec'45'trace_2818 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3626 ::
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3626 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2314 ->
  T_TreeTrace_2314 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3644 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2238 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3690 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2314 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3730 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2238] ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3770 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2238] ->
  [T_AbstractInstr_2238] ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3790 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3848
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2314 ->
  T_LocState_540 ->
  T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3856 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3856
du_exec'45'tree'45'flat'45'equiv'45'simple_3856 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3856
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
