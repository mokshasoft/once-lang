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
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Machine.SMCore.Slot
d_Slot_16 :: ()
d_Slot_16 = erased
-- Once.CCC.Machine.SMCore.HeapRegion
d_HeapRegion_18 = ()
data T_HeapRegion_18
  = C_heap'45'region_28 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
                        Integer
-- Once.CCC.Machine.SMCore.HeapRegion.region-ref
d_region'45'ref_24 ::
  T_HeapRegion_18 -> MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8
d_region'45'ref_24 v0
  = case coe v0 of
      C_heap'45'region_28 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.HeapRegion.region-size
d_region'45'size_26 :: T_HeapRegion_18 -> Integer
d_region'45'size_26 v0
  = case coe v0 of
      C_heap'45'region_28 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.InRegion
d_InRegion_30 a0 a1 = ()
newtype T_InRegion_30
  = C_in'45'region_38 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.CCC.Machine.SMCore.HeapOwnership
d_HeapOwnership_40 :: ()
d_HeapOwnership_40 = erased
-- Once.CCC.Machine.SMCore.OutsideOwned
d_OutsideOwned_42 a0 a1 = ()
data T_OutsideOwned_42
  = C_outside'45'nil_46 |
    C_outside'45'cons_54 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
                         T_OutsideOwned_42
-- Once.CCC.Machine.SMCore.AbstractReg
d_AbstractReg_56 = ()
data T_AbstractReg_56
  = C_Input1_58 | C_Input2_60 | C_Output_62 | C_Scratch_64
-- Once.CCC.Machine.SMCore.ValueLocation
d_ValueLocation_68 a0 = ()
data T_ValueLocation_68
  = C_AtStack_72 AgdaAny Integer |
    C_AtDynamic_74 MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_78 a0 = ()
data T_StoredValue_78
  = C_SV'45'Ptr_82 T_ValueLocation_68 | C_SV'45'Tag_84 Integer |
    C_SV'45'Lit_88 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_FitsInReg_192 AgdaAny |
    C_SV'45'Code_90 Integer
-- Once.CCC.Machine.SMCore.sucLoc
d_sucLoc_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_68 -> T_ValueLocation_68
d_sucLoc_94 ~v0 v1 = du_sucLoc_94 v1
du_sucLoc_94 :: T_ValueLocation_68 -> T_ValueLocation_68
du_sucLoc_94 v0
  = case coe v0 of
      C_AtStack_72 v1 v2
        -> coe
             C_AtStack_72 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      C_AtDynamic_74 v1
        -> coe
             C_AtDynamic_74
             (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.offsetLoc
d_offsetLoc_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_ValueLocation_68 -> Integer -> T_ValueLocation_68
d_offsetLoc_104 ~v0 v1 v2 = du_offsetLoc_104 v1 v2
du_offsetLoc_104 ::
  T_ValueLocation_68 -> Integer -> T_ValueLocation_68
du_offsetLoc_104 v0 v1
  = case coe v0 of
      C_AtStack_72 v2 v3
        -> coe C_AtStack_72 (coe v2) (coe addInt (coe v1) (coe v3))
      C_AtDynamic_74 v2
        -> coe
             C_AtDynamic_74
             (coe
                MAlonzo.Code.Once.Memory.HeapAddress.d_offsetHL_98 (coe v2)
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.StackMem
d_StackMem_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_StackMem_118 = erased
-- Once.CCC.Machine.SMCore.HeapMem
d_HeapMem_124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_HeapMem_124 = erased
-- Once.CCC.Machine.SMCore._≟R_
d__'8799'R__132 ::
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__132 v0 v1
  = case coe v0 of
      C_Input1_58
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Input2_60
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Output_62
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C_Scratch_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Scratch_64
        -> case coe v1 of
             C_Input1_58
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Input2_60
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Output_62
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Scratch_64
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_136 a0 = ()
data T_Registers_136
  = C_mkRegs_160 T_StoredValue_78 T_StoredValue_78 T_StoredValue_78
                 Integer T_StoredValue_78
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_150 :: T_Registers_136 -> T_StoredValue_78
d_input1_150 v0
  = case coe v0 of
      C_mkRegs_160 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_152 :: T_Registers_136 -> T_StoredValue_78
d_input2_152 v0
  = case coe v0 of
      C_mkRegs_160 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_154 :: T_Registers_136 -> T_StoredValue_78
d_output_154 v0
  = case coe v0 of
      C_mkRegs_160 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_156 :: T_Registers_136 -> Integer
d_stackSlot_156 v0
  = case coe v0 of
      C_mkRegs_160 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.scratch
d_scratch_158 :: T_Registers_136 -> T_StoredValue_78
d_scratch_158 v0
  = case coe v0 of
      C_mkRegs_160 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 -> T_AbstractReg_56 -> T_StoredValue_78
d_readReg_164 ~v0 v1 v2 = du_readReg_164 v1 v2
du_readReg_164 ::
  T_Registers_136 -> T_AbstractReg_56 -> T_StoredValue_78
du_readReg_164 v0 v1
  = case coe v1 of
      C_Input1_58 -> coe d_input1_150 (coe v0)
      C_Input2_60 -> coe d_input2_152 (coe v0)
      C_Output_62 -> coe d_output_154 (coe v0)
      C_Scratch_64 -> coe d_scratch_158 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 ->
  T_AbstractReg_56 -> T_StoredValue_78 -> T_Registers_136
d_writeReg_176 ~v0 v1 v2 = du_writeReg_176 v1 v2
du_writeReg_176 ::
  T_Registers_136 ->
  T_AbstractReg_56 -> T_StoredValue_78 -> T_Registers_136
du_writeReg_176 v0 v1
  = case coe v1 of
      C_Input1_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_160 (coe v2) (coe d_input2_152 (coe v0))
                  (coe d_output_154 (coe v0)) (coe d_stackSlot_156 (coe v0))
                  (coe d_scratch_158 (coe v0)))
      C_Input2_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_160 (coe d_input1_150 (coe v0)) (coe v2)
                  (coe d_output_154 (coe v0)) (coe d_stackSlot_156 (coe v0))
                  (coe d_scratch_158 (coe v0)))
      C_Output_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_160 (coe d_input1_150 (coe v0))
                  (coe d_input2_152 (coe v0)) (coe v2) (coe d_stackSlot_156 (coe v0))
                  (coe d_scratch_158 (coe v0)))
      C_Scratch_64
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_160 (coe d_input1_150 (coe v0))
                  (coe d_input2_152 (coe v0)) (coe d_output_154 (coe v0))
                  (coe d_stackSlot_156 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 -> Integer -> T_Registers_136
d_writeStackSlot_196 ~v0 v1 v2 = du_writeStackSlot_196 v1 v2
du_writeStackSlot_196 ::
  T_Registers_136 -> Integer -> T_Registers_136
du_writeStackSlot_196 v0 v1
  = coe
      C_mkRegs_160 (coe d_input1_150 (coe v0))
      (coe d_input2_152 (coe v0)) (coe d_output_154 (coe v0)) (coe v1)
      (coe d_scratch_158 (coe v0))
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 -> Integer -> T_Registers_136
d_incrStackSlot_204 ~v0 v1 v2 = du_incrStackSlot_204 v1 v2
du_incrStackSlot_204 ::
  T_Registers_136 -> Integer -> T_Registers_136
du_incrStackSlot_204 v0 v1
  = coe
      C_mkRegs_160 (coe d_input1_150 (coe v0))
      (coe d_input2_152 (coe v0)) (coe d_output_154 (coe v0))
      (coe addInt (coe d_stackSlot_156 (coe v0)) (coe v1))
      (coe d_scratch_158 (coe v0))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 -> Integer -> T_Registers_136
d_decrStackSlot_212 ~v0 v1 v2 = du_decrStackSlot_212 v1 v2
du_decrStackSlot_212 ::
  T_Registers_136 -> Integer -> T_Registers_136
du_decrStackSlot_212 v0 v1
  = coe
      C_mkRegs_160 (coe d_input1_150 (coe v0))
      (coe d_input2_152 (coe v0)) (coe d_output_154 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_156 (coe v0)) v1)
      (coe d_scratch_158 (coe v0))
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_232 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_354 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_380 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_408 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_434 = ()
data T_RegOp_434
  = C_scratch'45'one_436 | C_scratch'45'zero_438 |
    C_scratch'45'dec_440 | C_scratch'45'load'45'count_442 |
    C_input2'45'zero_444 | C_input2'45'inc_446
-- Once.CCC.Machine.SMCore.sv-succ
d_sv'45'succ_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_78 -> T_StoredValue_78
d_sv'45'succ_450 ~v0 v1 = du_sv'45'succ_450 v1
du_sv'45'succ_450 :: T_StoredValue_78 -> T_StoredValue_78
du_sv'45'succ_450 v0
  = let v1 = coe C_SV'45'Tag_84 (coe (1 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_84 v2
           -> coe C_SV'45'Tag_84 (coe addInt (coe (1 :: Integer)) (coe v2))
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-pred
d_sv'45'pred_456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_78 -> T_StoredValue_78
d_sv'45'pred_456 ~v0 v1 = du_sv'45'pred_456 v1
du_sv'45'pred_456 :: T_StoredValue_78 -> T_StoredValue_78
du_sv'45'pred_456 v0
  = let v1 = coe C_SV'45'Tag_84 (coe (0 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_84 v2
           -> case coe v2 of
                _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                    let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                    coe (coe C_SV'45'Tag_84 (coe v3))
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-tag-val
d_sv'45'tag'45'val_462 :: T_StoredValue_78 -> Integer
d_sv'45'tag'45'val_462 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_SV'45'Tag_84 v2 -> coe v2
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.LocState
d_LocState_468 a0 = ()
data T_LocState_468
  = C_mkLocState_488 T_Registers_136
                     (AgdaAny -> Integer -> Maybe T_StoredValue_78)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_78)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_480 :: T_LocState_468 -> T_Registers_136
d_regs_480 v0
  = case coe v0 of
      C_mkLocState_488 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_482 ::
  T_LocState_468 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_stackMem_482 v0
  = case coe v0 of
      C_mkLocState_488 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_484 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_heapMem_484 v0
  = case coe v0 of
      C_mkLocState_488 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_486 :: T_LocState_468 -> Bool
d_halted_486 v0
  = case coe v0 of
      C_mkLocState_488 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_434 -> T_Registers_136 -> T_Registers_136
d_setReg_492 ~v0 v1 v2 = du_setReg_492 v1 v2
du_setReg_492 :: T_RegOp_434 -> T_Registers_136 -> T_Registers_136
du_setReg_492 v0 v1
  = case coe v0 of
      C_scratch'45'one_436
        -> coe
             du_writeReg_176 v1 (coe C_Scratch_64)
             (coe C_SV'45'Tag_84 (coe (1 :: Integer)))
      C_scratch'45'zero_438
        -> coe
             du_writeReg_176 v1 (coe C_Scratch_64)
             (coe C_SV'45'Tag_84 (coe (0 :: Integer)))
      C_scratch'45'dec_440
        -> coe
             du_writeReg_176 v1 (coe C_Scratch_64)
             (coe
                du_sv'45'pred_456 (coe du_readReg_164 (coe v1) (coe C_Scratch_64)))
      C_scratch'45'load'45'count_442
        -> coe
             du_writeReg_176 v1 (coe C_Scratch_64)
             (coe du_readReg_164 (coe v1) (coe C_Input2_60))
      C_input2'45'zero_444
        -> coe
             du_writeReg_176 v1 (coe C_Input2_60)
             (coe C_SV'45'Tag_84 (coe (0 :: Integer)))
      C_input2'45'inc_446
        -> coe
             du_writeReg_176 v1 (coe C_Input2_60)
             (coe
                du_sv'45'succ_450 (coe du_readReg_164 (coe v1) (coe C_Input2_60)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_434 -> T_LocState_468 -> T_LocState_468
d_exec'45'reg'45'op_508 ~v0 v1 v2 = du_exec'45'reg'45'op_508 v1 v2
du_exec'45'reg'45'op_508 ::
  T_RegOp_434 -> T_LocState_468 -> T_LocState_468
du_exec'45'reg'45'op_508 v0 v1
  = coe
      C_mkLocState_488
      (coe du_setReg_492 (coe v0) (coe d_regs_480 (coe v1)))
      (coe d_stackMem_482 (coe v1)) (coe d_heapMem_484 (coe v1))
      (coe d_halted_486 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_514 = ()
data T_AllocMode_514 = C_Stack_516 | C_Heap_518
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_522 a0 = ()
data T_AllocState_522 = C_mkAllocState_586 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_580 :: T_AllocState_522 -> AgdaAny
d_current'45'frame_580 v0
  = case coe v0 of
      C_mkAllocState_586 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_582 :: T_AllocState_522 -> Integer
d_next'45'slot_582 v0
  = case coe v0 of
      C_mkAllocState_586 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_584 :: T_AllocState_522 -> Integer
d_next'45'heap'45'ref_584 v0
  = case coe v0 of
      C_mkAllocState_586 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_616 ::
  T_LocState_468 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_616 v0 v1 v2 = coe d_stackMem_482 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_624 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_624 v0 v1 = coe d_heapMem_484 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_630 ~v0 v1 v2 = du_readLoc_630 v1 v2
du_readLoc_630 ::
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_630 v0 v1
  = case coe v1 of
      C_AtStack_72 v2 v3 -> coe d_stackMem_482 v0 v2 v3
      C_AtDynamic_74 v2 -> coe d_heapMem_484 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_650 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_650 v5 v6 v7 v8
du_writeStackMem'45'aux_650 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_650 v0 v1 v2 v3
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
d_writeStackMem_658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_658 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_650
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_676 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_676 v3 v4 v5
du_writeHeapMem'45'aux_676 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_676 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_682 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_682 v1 v2 v3 v4
du_writeHeapMem_682 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_682 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_676
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_468
d_writeLocToStack_692 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_488 (coe d_regs_480 (coe v1))
      (coe
         d_writeStackMem_658 (coe v0) (coe d_stackMem_482 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_484 (coe v1)) (coe d_halted_486 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
d_writeLocToHeap_702 ~v0 v1 v2 v3 = du_writeLocToHeap_702 v1 v2 v3
du_writeLocToHeap_702 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
du_writeLocToHeap_702 v0 v1 v2
  = coe
      C_mkLocState_488 (coe d_regs_480 (coe v0))
      (coe d_stackMem_482 (coe v0))
      (coe
         du_writeHeapMem_682 (coe d_heapMem_484 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_486 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_468
d_writeLoc_710 v0 v1 v2 v3
  = case coe v2 of
      C_AtStack_72 v4 v5
        -> coe
             d_writeLocToStack_692 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_AtDynamic_74 v4
        -> case coe v3 of
             C_SV'45'Ptr_82 v5
               -> case coe v5 of
                    C_AtStack_72 v6 v7 -> coe v1
                    C_AtDynamic_74 v6
                      -> coe du_writeLocToHeap_702 (coe v1) (coe v4) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Tag_84 v5
               -> coe du_writeLocToHeap_702 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_88 v5 v6 v7
               -> coe du_writeLocToHeap_702 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_90 v5
               -> coe du_writeLocToHeap_702 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_756 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_794 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_834 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_834 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_854 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_854 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_882 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_914 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1154 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1206 a0 = ()
data T_LocSourceExt_1206
  = C_Loc_1210 T_ValueLocation_68 | C_IndReg_1212 T_AbstractReg_56 |
    C_IndRegSuc_1214 T_AbstractReg_56
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_78 -> Maybe T_ValueLocation_68
d_sv'45'as'45'loc_1218 ~v0 v1 = du_sv'45'as'45'loc_1218 v1
du_sv'45'as'45'loc_1218 ::
  T_StoredValue_78 -> Maybe T_ValueLocation_68
du_sv'45'as'45'loc_1218 v0
  = case coe v0 of
      C_SV'45'Ptr_82 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_SV'45'Tag_84 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Lit_88 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_SV'45'Code_90 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.resolveSourceExt
d_resolveSourceExt_1224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 -> T_LocSourceExt_1206 -> Maybe T_ValueLocation_68
d_resolveSourceExt_1224 ~v0 v1 v2 = du_resolveSourceExt_1224 v1 v2
du_resolveSourceExt_1224 ::
  T_Registers_136 -> T_LocSourceExt_1206 -> Maybe T_ValueLocation_68
du_resolveSourceExt_1224 v0 v1
  = case coe v1 of
      C_Loc_1210 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1212 v2
        -> coe
             du_sv'45'as'45'loc_1218 (coe du_readReg_164 (coe v0) (coe v2))
      C_IndRegSuc_1214 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1218 (coe du_readReg_164 (coe v0) (coe v2)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe du_sucLoc_94 (coe v4))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Instr
d_Instr_1254 a0 = ()
data T_Instr_1254
  = C_load_1258 T_AbstractReg_56 T_LocSourceExt_1206 |
    C_store_1260 T_LocSourceExt_1206 T_AbstractReg_56 |
    C_mov_1262 T_AbstractReg_56 T_AbstractReg_56
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1270 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_1270 v0 v1 = coe d_heapMem_484 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_1272 ~v0 = du_readLoc_1272
du_readLoc_1272 ::
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_1272 = coe du_readLoc_630
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1274 ::
  T_LocState_468 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_1274 v0 v1 v2 = coe d_stackMem_482 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_1276 ~v0 = du_writeHeapMem_1276
du_writeHeapMem_1276 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_1276 = coe du_writeHeapMem_682
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_1278 ~v0 = du_writeHeapMem'45'aux_1278
du_writeHeapMem'45'aux_1278 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_1278 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_676 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_468
d_writeLoc_1280 v0 = coe d_writeLoc_710 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1282 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1284 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1284 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1286 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1288 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1290 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1292 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1294 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1294 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
d_writeLocToHeap_1296 ~v0 = du_writeLocToHeap_1296
du_writeLocToHeap_1296 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
du_writeLocToHeap_1296 = coe du_writeLocToHeap_702
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_468
d_writeLocToStack_1298 v0 = coe d_writeLocToStack_692 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_1300 v0 = coe d_writeStackMem_658 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_1302 ~v0 = du_writeStackMem'45'aux_1302
du_writeStackMem'45'aux_1302 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_1302 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_650 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'with'45'value_1304 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1304 v1 v2
du_exec'45'load'45'with'45'value_1304 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'with'45'value_1304 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_488 (coe du_writeReg_176 (d_regs_480 (coe v3)) v0 v2)
                  (coe d_stackMem_482 (coe v3)) (coe d_heapMem_484 (coe v3))
                  (coe d_halted_486 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_488 (coe d_regs_480 (coe v2))
                  (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'via'45'resolved_1316 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1316 v1 v2
du_exec'45'load'45'via'45'resolved_1316 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'via'45'resolved_1316 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1304 v0
                  (coe du_readLoc_630 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_488 (coe d_regs_480 (coe v2))
                  (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'store'45'via'45'resolved_1328 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_710 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_488 (coe d_regs_480 (coe v3))
                  (coe d_stackMem_482 (coe v3)) (coe d_heapMem_484 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 -> Maybe T_ValueLocation_68
d_slot'45'base_1338 ~v0 v1 = du_slot'45'base_1338 v1
du_slot'45'base_1338 ::
  Maybe T_StoredValue_78 -> Maybe T_ValueLocation_68
du_slot'45'base_1338 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1218 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  Integer -> T_LocState_468 -> T_LocState_468
d_exec'45'lea'45'indexed'45'via_1342 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1342 v1
du_exec'45'lea'45'indexed'45'via_1342 ::
  Maybe T_ValueLocation_68 ->
  Integer -> T_LocState_468 -> T_LocState_468
du_exec'45'lea'45'indexed'45'via_1342 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_488
                  (coe
                     du_writeReg_176 (d_regs_480 (coe v3)) (coe C_Input1_58)
                     (coe C_SV'45'Ptr_82 (coe du_offsetLoc_104 (coe v1) (coe v2))))
                  (coe d_stackMem_482 (coe v3)) (coe d_heapMem_484 (coe v3))
                  (coe d_halted_486 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_488 (coe d_regs_480 (coe v2))
                  (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'suc'45'via'45'resolved_1354 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1354 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1354 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'suc'45'via'45'resolved_1354 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1304 v0
                  (coe du_readLoc_630 (coe v3) (coe du_sucLoc_94 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_488 (coe d_regs_480 (coe v2))
                  (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'store'45'suc'45'via'45'resolved_1366 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_710
                  (coe v0) (coe v4) (coe du_sucLoc_94 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_488 (coe d_regs_480 (coe v3))
                  (coe d_stackMem_482 (coe v3)) (coe d_heapMem_484 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1254 -> T_LocState_468 -> T_LocState_468
d_exec_1376 v0 v1
  = case coe v1 of
      C_load_1258 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1316 v2
                  (coe du_resolveSourceExt_1224 (coe d_regs_480 (coe v4)) (coe v3))
                  v4)
      C_store_1260 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1328 v0
                  (coe du_resolveSourceExt_1224 (coe d_regs_480 (coe v4)) (coe v2))
                  (coe du_readReg_164 (coe d_regs_480 (coe v4)) (coe v3)) v4)
      C_mov_1262 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_488
                  (coe
                     du_writeReg_176 (d_regs_480 (coe v4)) v2
                     (coe du_readReg_164 (coe d_regs_480 (coe v4)) (coe v3)))
                  (coe d_stackMem_482 (coe v4)) (coe d_heapMem_484 (coe v4))
                  (coe d_halted_486 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1402 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1408 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1254] -> T_LocState_468 -> T_LocState_468
d_execList_1410 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_486 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1410 (coe v0) (coe v4) (coe d_exec_1376 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1442 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_1442 v0 v1 = coe d_heapMem_484 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_1444 ~v0 = du_readLoc_1444
du_readLoc_1444 ::
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_1444 = coe du_readLoc_630
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1446 ::
  T_LocState_468 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_1446 v0 v1 v2 = coe d_stackMem_482 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_1448 ~v0 = du_writeHeapMem_1448
du_writeHeapMem_1448 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_1448 = coe du_writeHeapMem_682
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_1450 ~v0 = du_writeHeapMem'45'aux_1450
du_writeHeapMem'45'aux_1450 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_1450 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_676 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_468
d_writeLoc_1452 v0 = coe d_writeLoc_710 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1454 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1456 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1456 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1458 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1460 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1462 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1464 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1466 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1466 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
d_writeLocToHeap_1468 ~v0 = du_writeLocToHeap_1468
du_writeLocToHeap_1468 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
du_writeLocToHeap_1468 = coe du_writeLocToHeap_702
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_468
d_writeLocToStack_1470 v0 = coe d_writeLocToStack_692 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_1472 v0 = coe d_writeStackMem_658 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_1474 ~v0 = du_writeStackMem'45'aux_1474
du_writeStackMem'45'aux_1474 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_1474 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_650 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1254 -> T_LocState_468 -> T_LocState_468
d_exec_1478 v0 = coe d_exec_1376 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  Integer -> T_LocState_468 -> T_LocState_468
d_exec'45'lea'45'indexed'45'via_1480 ~v0
  = du_exec'45'lea'45'indexed'45'via_1480
du_exec'45'lea'45'indexed'45'via_1480 ::
  Maybe T_ValueLocation_68 ->
  Integer -> T_LocState_468 -> T_LocState_468
du_exec'45'lea'45'indexed'45'via_1480
  = coe du_exec'45'lea'45'indexed'45'via_1342
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1482 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1484 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'suc'45'via'45'resolved_1486 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1486
du_exec'45'load'45'suc'45'via'45'resolved_1486 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'suc'45'via'45'resolved_1486
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1354
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'via'45'resolved_1488 ~v0
  = du_exec'45'load'45'via'45'resolved_1488
du_exec'45'load'45'via'45'resolved_1488 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'via'45'resolved_1488
  = coe du_exec'45'load'45'via'45'resolved_1316
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'with'45'value_1490 ~v0
  = du_exec'45'load'45'with'45'value_1490
du_exec'45'load'45'with'45'value_1490 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'with'45'value_1490
  = coe du_exec'45'load'45'with'45'value_1304
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'store'45'suc'45'via'45'resolved_1492 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1366 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'store'45'via'45'resolved_1494 v0
  = coe d_exec'45'store'45'via'45'resolved_1328 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1254] -> T_LocState_468 -> T_LocState_468
d_execList_1496 v0 = coe d_execList_1410 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 -> Maybe T_ValueLocation_68
d_slot'45'base_1498 ~v0 = du_slot'45'base_1498
du_slot'45'base_1498 ::
  Maybe T_StoredValue_78 -> Maybe T_ValueLocation_68
du_slot'45'base_1498 = coe du_slot'45'base_1338
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_LocSourceExt_1206 -> Maybe T_StoredValue_78
d_resolved'45'readLoc_1500 ~v0 v1 v2
  = du_resolved'45'readLoc_1500 v1 v2
du_resolved'45'readLoc_1500 ::
  T_LocState_468 -> T_LocSourceExt_1206 -> Maybe T_StoredValue_78
du_resolved'45'readLoc_1500 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1224 (coe d_regs_480 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_630 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1530 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1600 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_LocState_468 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1676 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1706 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1762 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1814 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1866 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 ->
  T_AbstractReg_56 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1882 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1900 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1914 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1932 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1998 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2022 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2050 = ()
data T_FlatCtrl_2050
  = C_c'45'label_2052 Integer | C_c'45'jmp_2054 Integer |
    C_c'45'branch'45'scratch'45'zero_2056 Integer |
    C_c'45'branch'45'tag'45'zero_2058 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2060 = ()
data T_AbstractInstr_2060
  = C_mov'45'to'45'output_2062 | C_mov'45'to'45'input_2064 |
    C_mov'45'output'45'to'45'input2_2066 |
    C_mov'45'input2'45'to'45'output_2068 | C_load'45'indirect_2070 |
    C_load'45'indirect'45'suc_2072 |
    C_load'45'from'45'slot_2074 Integer |
    C_store'45'at'45'slot_2076 Integer | C_store'45'indirect_2078 |
    C_store'45'indirect'45'suc_2080 | C_lea'45'slot_2082 Integer |
    C_restore'45'input_2084 Integer |
    C_instr'45'alloc'45'stack_2086 Integer |
    C_instr'45'dealloc'45'stack_2088 Integer |
    C_instr'45'reclaim'45'to_2090 Integer |
    C_instr'45'push'45'frame_2092 Integer |
    C_instr'45'pop'45'frame_2094 | C_instr'45'call'45'closure_2096 |
    C_worklist'45'init_2098 Integer | C_worklist'45'push_2100 Integer |
    C_worklist'45'pop_2102 Integer | C_worklist'45'check_2104 Integer |
    C_instr'45'sigop_2110 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 |
    C_instr'45'load'45'const_2114 MAlonzo.Code.Once.Type.T_Type_112
                                  MAlonzo.Code.Once.Type.T_FitsInReg_192 AgdaAny |
    C_instr'45'load'45'code'45'addr_2116 Integer |
    C_instr'45'save'45'closure'45'reg_2118 |
    C_instr'45'load'45'tag'45'lit_2120 Integer |
    C_instr'45'case'45'on'45'tag_2122 [T_AbstractInstr_2060]
                                      [T_AbstractInstr_2060] |
    C_instr'45'alloc'45'heap_2124 Integer |
    C_instr'45'loop_2126 [T_AbstractInstr_2060] |
    C_instr'45'reg'45'op_2128 T_RegOp_434 |
    C_instr'45'ctrl_2130 T_FlatCtrl_2050 |
    C_lea'45'indexed_2132 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2134 :: ()
d_AbstractTrace_2134 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2136 = ()
data T_TreeTrace_2136
  = C_ε_2138 | C_instr_2140 T_AbstractInstr_2060 |
    C__'9656'__2142 T_TreeTrace_2136 T_TreeTrace_2136 |
    C_branch_2144 Integer T_TreeTrace_2136 T_TreeTrace_2136 |
    C_call'45'sub_2146 T_TreeTrace_2136 |
    C_flat_2148 [T_AbstractInstr_2060]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2150 :: [T_AbstractInstr_2060] -> T_TreeTrace_2136
d_flatToTree_2150 v0
  = case coe v0 of
      [] -> coe C_ε_2138
      (:) v1 v2
        -> coe
             C__'9656'__2142 (coe C_instr_2140 (coe v1))
             (coe d_flatToTree_2150 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2156 :: T_TreeTrace_2136 -> [T_AbstractInstr_2060]
d_treeToFlat_2156 v0
  = case coe v0 of
      C_ε_2138 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2140 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2142 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2156 (coe v1)) (coe d_treeToFlat_2156 (coe v2))
      C_branch_2144 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2156 (coe v2)) (coe d_treeToFlat_2156 (coe v3))
      C_call'45'sub_2146 v1 -> coe d_treeToFlat_2156 (coe v1)
      C_flat_2148 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2172 ::
  Integer -> T_TreeTrace_2136 -> [T_AbstractInstr_2060]
d_treeToRunnable_2172 v0 v1
  = case coe v1 of
      C_ε_2138 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2140 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2142 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2172 (coe v0) (coe v2))
             (coe d_treeToRunnable_2172 (coe v0) (coe v3))
      C_branch_2144 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2172 (coe v0) (coe v3))
             (coe d_treeToRunnable_2172 (coe v0) (coe v4))
      C_call'45'sub_2146 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2100 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2172 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2102 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2148 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2202 ::
  Integer -> T_TreeTrace_2136 -> [T_AbstractInstr_2060]
d_treeToRunnableWithInit_2202 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2098 (coe v0))
      (coe d_treeToRunnable_2172 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2238 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_2238 v0 v1 = coe d_heapMem_484 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_2240 ~v0 = du_readLoc_2240
du_readLoc_2240 ::
  T_LocState_468 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_2240 = coe du_readLoc_630
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2242 ::
  T_LocState_468 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_2242 v0 v1 v2 = coe d_stackMem_482 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_2244 ~v0 = du_writeHeapMem_2244
du_writeHeapMem_2244 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_2244 = coe du_writeHeapMem_682
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_2246 ~v0 = du_writeHeapMem'45'aux_2246
du_writeHeapMem'45'aux_2246 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_2246 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_676 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_468
d_writeLoc_2248 v0 = coe d_writeLoc_710 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2250 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2252 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2252 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2254 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2256 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2258 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2260 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2262 ::
  T_LocState_468 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2262 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
d_writeLocToHeap_2264 ~v0 = du_writeLocToHeap_2264
du_writeLocToHeap_2264 ::
  T_LocState_468 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_468
du_writeLocToHeap_2264 = coe du_writeLocToHeap_702
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_468
d_writeLocToStack_2266 v0 = coe d_writeLocToStack_692 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_2268 v0 = coe d_writeStackMem_658 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_2270 ~v0 = du_writeStackMem'45'aux_2270
du_writeStackMem'45'aux_2270 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_2270 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_650 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1254 -> T_LocState_468 -> T_LocState_468
d_exec_2274 v0 = coe d_exec_1376 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  Integer -> T_LocState_468 -> T_LocState_468
d_exec'45'lea'45'indexed'45'via_2276 ~v0
  = du_exec'45'lea'45'indexed'45'via_2276
du_exec'45'lea'45'indexed'45'via_2276 ::
  Maybe T_ValueLocation_68 ->
  Integer -> T_LocState_468 -> T_LocState_468
du_exec'45'lea'45'indexed'45'via_2276
  = coe du_exec'45'lea'45'indexed'45'via_1342
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2278 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2280 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'suc'45'via'45'resolved_2282 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2282
du_exec'45'load'45'suc'45'via'45'resolved_2282 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'suc'45'via'45'resolved_2282
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1354
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'via'45'resolved_2284 ~v0
  = du_exec'45'load'45'via'45'resolved_2284
du_exec'45'load'45'via'45'resolved_2284 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'via'45'resolved_2284
  = coe du_exec'45'load'45'via'45'resolved_1316
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'load'45'with'45'value_2286 ~v0
  = du_exec'45'load'45'with'45'value_2286
du_exec'45'load'45'with'45'value_2286 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
du_exec'45'load'45'with'45'value_2286
  = coe du_exec'45'load'45'with'45'value_1304
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'store'45'suc'45'via'45'resolved_2288 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1366 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_468 -> T_LocState_468
d_exec'45'store'45'via'45'resolved_2290 v0
  = coe d_exec'45'store'45'via'45'resolved_1328 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1254] -> T_LocState_468 -> T_LocState_468
d_execList_2292 v0 = coe d_execList_1410 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 -> Maybe T_ValueLocation_68
d_slot'45'base_2294 ~v0 = du_slot'45'base_2294
du_slot'45'base_2294 ::
  Maybe T_StoredValue_78 -> Maybe T_ValueLocation_68
du_slot'45'base_2294 = coe du_slot'45'base_1338
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2298 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_LocState_468 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2300 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2302 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2304 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2306 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2308 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2310 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1206 ->
  T_ValueLocation_68 ->
  T_LocState_468 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2312 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2314 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 ->
  T_AbstractReg_56 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2316 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2318 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_468 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2320 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 ->
  T_LocState_468 ->
  T_ValueLocation_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2322 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_LocSourceExt_1206 -> Maybe T_StoredValue_78
d_resolved'45'readLoc_2324 ~v0 = du_resolved'45'readLoc_2324
du_resolved'45'readLoc_2324 ::
  T_LocState_468 -> T_LocSourceExt_1206 -> Maybe T_StoredValue_78
du_resolved'45'readLoc_2324 = coe du_resolved'45'readLoc_1500
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2326 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2326 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2326 ::
  Maybe T_StoredValue_78 ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2326 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe du_writeReg_176 (d_regs_480 (coe v1)) (coe C_Output_62) v3)
                (coe d_stackMem_482 (coe v1)) (coe d_heapMem_484 (coe v1))
                (coe d_halted_486 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488 (coe d_regs_480 (coe v1))
                (coe d_stackMem_482 (coe v1)) (coe d_heapMem_484 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2338 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2338 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2338 ::
  Maybe T_StoredValue_78 ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2338 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe du_writeReg_176 (d_regs_480 (coe v1)) (coe C_Input1_58) v3)
                (coe d_stackMem_482 (coe v1)) (coe d_heapMem_484 (coe v1))
                (coe d_halted_486 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488 (coe d_regs_480 (coe v1))
                (coe d_stackMem_482 (coe v1)) (coe d_heapMem_484 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2356 ::
  T_StoredValue_78 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2356 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2362 ::
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2362 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2370 ::
  T_StoredValue_78 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2370 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2376 ::
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2376 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_78
d_unit'45'storedvalue_2378 ~v0 = du_unit'45'storedvalue_2378
du_unit'45'storedvalue_2378 :: T_StoredValue_78
du_unit'45'storedvalue_2378
  = coe
      C_SV'45'Lit_88 (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_194) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2384
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  T_LocState_468 -> T_StoredValue_78
d_pure'45'sigop'45'output_2390 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_200 (coe v2) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
           -> coe du_unit'45'storedvalue_2378
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe d_structured'45'pure'45'sigop'45'output_2384 v0 v1 v2 v3 v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_140 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  T_LocState_468 -> T_StoredValue_78
d_exec'45'sigop'45'output'45'of_2424 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_144
        -> coe
             d_pure'45'sigop'45'output_2390 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Emits_146
        -> coe du_unit'45'storedvalue_2378
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_148
        -> coe du_unit'45'storedvalue_2378
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  T_LocState_468 -> T_StoredValue_78
d_exec'45'sigop'45'output_2434 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2424 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_170 (coe v3))
      (coe v3) (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_140 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  T_LocState_468 -> Bool
d_exec'45'sigop'45'halts'45'of_2444 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2444 v3
du_exec'45'sigop'45'halts'45'of_2444 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_140 -> Bool
du_exec'45'sigop'45'halts'45'of_2444 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_148
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  T_LocState_468 -> Bool
d_exec'45'sigop'45'halts_2450 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2450 v3
du_exec'45'sigop'45'halts_2450 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 -> Bool
du_exec'45'sigop'45'halts_2450 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2444
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_170 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> Maybe T_StoredValue_78
d_case'45'tag'45'at_2456 ~v0 v1 = du_case'45'tag'45'at_2456 v1
du_case'45'tag'45'at_2456 ::
  T_LocState_468 -> Maybe T_StoredValue_78
du_case'45'tag'45'at_2456 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1218
              (coe d_input1_150 (coe d_regs_480 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_630 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2060 ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2470 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2062
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Input1_58)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2064
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Input1_58)
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Output_62)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_2066
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Input2_60)
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Output_62)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_2068
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Input2_60)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_load'45'indirect_2070
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1316 (coe C_Output_62)
                (coe
                   du_sv'45'as'45'loc_1218
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Input1_58)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2072
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1354 (coe C_Output_62)
                (coe
                   du_sv'45'as'45'loc_1218
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Input1_58)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2074 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2326
             (coe
                du_readLoc_630 (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2076 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_710 (coe v0) (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4))
                (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Output_62)))
             (coe v3)
      C_store'45'indirect_2078
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1328 v0
                (coe
                   du_sv'45'as'45'loc_1218
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Input1_58)))
                (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Output_62))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2080
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1366 v0
                (coe
                   du_sv'45'as'45'loc_1218
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Input1_58)))
                (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Output_62))
                v2)
             (coe v3)
      C_lea'45'slot_2082 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe
                      C_SV'45'Ptr_82
                      (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4))))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_restore'45'input_2084 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2338
             (coe
                du_readLoc_630 (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2086 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe du_incrStackSlot_204 (coe d_regs_480 (coe v2)) (coe v4))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe
                C_mkAllocState_586 (coe d_current'45'frame_580 (coe v3))
                (coe addInt (coe d_next'45'slot_582 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_584 (coe v3)))
      C_instr'45'dealloc'45'stack_2088 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe du_decrStackSlot_212 (coe d_regs_480 (coe v2)) (coe v4))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_2090 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_586 (coe d_current'45'frame_580 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_584 (coe v3)))
      C_instr'45'push'45'frame_2092 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeStackSlot_196 (coe d_regs_480 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_2094
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2096
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2098 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2100 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_710 (coe v0) (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4))
                (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Output_62)))
             (coe v3)
      C_worklist'45'pop_2102 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2326
             (coe
                du_readLoc_630 (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2104 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2110 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (d_exec'45'sigop'45'output_2434
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe du_exec'45'sigop'45'halts_2450 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2114 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Lit_88 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2116 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Code_90 (coe v4)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2120 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Tag_84 (coe v4)))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2122 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2476 (coe v0)
             (coe du_case'45'tag'45'at_2456 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2124 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488
                (coe
                   du_writeReg_176 (d_regs_480 (coe v2)) (coe C_Output_62)
                   (coe
                      C_SV'45'Ptr_82
                      (coe
                         C_AtDynamic_74
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_584 (coe v3)))))))
                (coe d_stackMem_482 (coe v2)) (coe d_heapMem_484 (coe v2))
                (coe d_halted_486 (coe v2)))
             (coe
                C_mkAllocState_586 (coe d_current'45'frame_580 (coe v3))
                (coe d_next'45'slot_582 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_584 (coe v3))))))
      C_instr'45'loop_2126 v4
        -> coe
             d_exec'45'loop_2474 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2128 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_508 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2130 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2132 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1342
                (coe
                   du_slot'45'base_1338
                   (coe
                      du_readLoc_630 (coe v2)
                      (coe C_AtStack_72 (coe d_current'45'frame_580 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_462
                   (coe du_readReg_164 (coe d_regs_480 (coe v2)) (coe C_Scratch_64)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2060] ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2472 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_486 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2472 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2470 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2470 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2060] ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2474 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488 (coe d_regs_480 (coe v3))
                (coe d_stackMem_482 (coe v3)) (coe d_heapMem_484 (coe v3))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v4)
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6 = d_halted_486 (coe v3) in
              coe
                (if coe v6
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4)
                   else (let v7 = d_scratch_158 (coe d_regs_480 (coe v3)) in
                         coe
                           (let v8
                                  = d_exec'45'loop_2474
                                      (coe v0) (coe v5) (coe v2)
                                      (coe
                                         C_mkLocState_488
                                         (coe
                                            d_regs_480
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2472 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe d_stackMem_482 (coe v3))
                                         (coe
                                            d_heapMem_484
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2472 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe
                                            d_halted_486
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2472 (coe v0) (coe v2) (coe v3)
                                                  (coe v4)))))
                                      (coe
                                         C_mkAllocState_586 (coe d_current'45'frame_580 (coe v4))
                                         (coe d_next'45'slot_582 (coe v4))
                                         (coe
                                            d_next'45'heap'45'ref_584
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_exec'45'trace_2472 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))) in
                            coe
                              (case coe v7 of
                                 C_SV'45'Tag_84 v9
                                   -> case coe v9 of
                                        0 -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                               (coe v4)
                                        _ -> coe v8
                                 _ -> coe v8)))))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_2476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 ->
  [T_AbstractInstr_2060] ->
  [T_AbstractInstr_2060] ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2476 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_82 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_488 (coe d_regs_480 (coe v4))
                       (coe d_stackMem_482 (coe v4)) (coe d_heapMem_484 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Tag_84 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_2472 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2472 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_88 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_488 (coe d_regs_480 (coe v4))
                       (coe d_stackMem_482 (coe v4)) (coe d_heapMem_484 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Code_90 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_488 (coe d_regs_480 (coe v4))
                       (coe d_stackMem_482 (coe v4)) (coe d_heapMem_484 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_488 (coe d_regs_480 (coe v4))
                (coe d_stackMem_482 (coe v4)) (coe d_heapMem_484 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2060 ->
  [T_AbstractInstr_2060] ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2818 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2060 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2864 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_2898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2060 -> ()) -> [T_AbstractInstr_2060] -> ()
d_AllI_2898 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_2926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_522 -> AgdaAny) ->
  (T_AbstractInstr_2060 -> ()) ->
  (T_AbstractInstr_2060 ->
   T_LocState_468 ->
   T_AllocState_522 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2060] ->
  AgdaAny ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_2926 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_522 -> AgdaAny) ->
  (T_AbstractInstr_2060 -> ()) ->
  (T_AbstractInstr_2060 ->
   T_LocState_468 ->
   T_AllocState_522 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2060] ->
  [T_AbstractInstr_2060] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3016 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_468 -> T_AllocState_522 -> Integer -> Maybe Integer
d_getTag_3148 ~v0 v1 v2 v3 = du_getTag_3148 v1 v2 v3
du_getTag_3148 ::
  T_LocState_468 -> T_AllocState_522 -> Integer -> Maybe Integer
du_getTag_3148 v0 v1 v2
  = let v3
          = coe d_stackMem_482 v0 (d_current'45'frame_580 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2136 ->
  T_LocState_468 ->
  T_AllocState_522 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3172 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2140 v4
        -> let v5 = d_halted_486 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2470 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2142 v4 v5
        -> let v6 = d_halted_486 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3172 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3172 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3172 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2144 v4 v5 v6
        -> let v7 = d_halted_486 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_482 v2 (d_current'45'frame_580 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3172 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3172 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3172 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3172 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3172 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2146 v4
        -> let v5 = d_halted_486 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3172 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2148 v4
        -> coe d_exec'45'trace_2472 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3332 ::
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3332 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2136 ->
  T_TreeTrace_2136 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3350 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2060 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3396 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2136 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3436 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2060] ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3476 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2060] ->
  [T_AbstractInstr_2060] ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3496 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3554
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2136 ->
  T_LocState_468 ->
  T_AllocState_522 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3562 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3562
du_exec'45'tree'45'flat'45'equiv'45'simple_3562 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3562
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
