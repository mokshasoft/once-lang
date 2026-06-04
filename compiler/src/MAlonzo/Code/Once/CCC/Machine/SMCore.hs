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
    C_SV'45'Lit_88 MAlonzo.Code.Once.Type.T_Type_108
                   MAlonzo.Code.Once.Type.T_FitsInReg_188 AgdaAny |
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
-- Once.CCC.Machine.SMCore.LocState
d_LocState_462 a0 = ()
data T_LocState_462
  = C_mkLocState_482 T_Registers_136
                     (AgdaAny -> Integer -> Maybe T_StoredValue_78)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_78)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_474 :: T_LocState_462 -> T_Registers_136
d_regs_474 v0
  = case coe v0 of
      C_mkLocState_482 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_476 ::
  T_LocState_462 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_stackMem_476 v0
  = case coe v0 of
      C_mkLocState_482 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_478 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_heapMem_478 v0
  = case coe v0 of
      C_mkLocState_482 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_480 :: T_LocState_462 -> Bool
d_halted_480 v0
  = case coe v0 of
      C_mkLocState_482 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_434 -> T_Registers_136 -> T_Registers_136
d_setReg_486 ~v0 v1 v2 = du_setReg_486 v1 v2
du_setReg_486 :: T_RegOp_434 -> T_Registers_136 -> T_Registers_136
du_setReg_486 v0 v1
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
d_exec'45'reg'45'op_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_434 -> T_LocState_462 -> T_LocState_462
d_exec'45'reg'45'op_502 ~v0 v1 v2 = du_exec'45'reg'45'op_502 v1 v2
du_exec'45'reg'45'op_502 ::
  T_RegOp_434 -> T_LocState_462 -> T_LocState_462
du_exec'45'reg'45'op_502 v0 v1
  = coe
      C_mkLocState_482
      (coe du_setReg_486 (coe v0) (coe d_regs_474 (coe v1)))
      (coe d_stackMem_476 (coe v1)) (coe d_heapMem_478 (coe v1))
      (coe d_halted_480 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_508 = ()
data T_AllocMode_508 = C_Stack_510 | C_Heap_512
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_516 a0 = ()
data T_AllocState_516 = C_mkAllocState_580 AgdaAny Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_574 :: T_AllocState_516 -> AgdaAny
d_current'45'frame_574 v0
  = case coe v0 of
      C_mkAllocState_580 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_576 :: T_AllocState_516 -> Integer
d_next'45'slot_576 v0
  = case coe v0 of
      C_mkAllocState_580 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_578 :: T_AllocState_516 -> Integer
d_next'45'heap'45'ref_578 v0
  = case coe v0 of
      C_mkAllocState_580 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_610 ::
  T_LocState_462 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_610 v0 v1 v2 = coe d_stackMem_476 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_618 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_618 v0 v1 = coe d_heapMem_478 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_624 ~v0 v1 v2 = du_readLoc_624 v1 v2
du_readLoc_624 ::
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_624 v0 v1
  = case coe v1 of
      C_AtStack_72 v2 v3 -> coe d_stackMem_476 v0 v2 v3
      C_AtDynamic_74 v2 -> coe d_heapMem_478 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_644 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_644 v5 v6 v7 v8
du_writeStackMem'45'aux_644 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_644 v0 v1 v2 v3
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
d_writeStackMem_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_652 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_644
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__68 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_670 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_670 v3 v4 v5
du_writeHeapMem'45'aux_670 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_670 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_676 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_676 v1 v2 v3 v4
du_writeHeapMem_676 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_676 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_670
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_686 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_462
d_writeLocToStack_686 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_482 (coe d_regs_474 (coe v1))
      (coe
         d_writeStackMem_652 (coe v0) (coe d_stackMem_476 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_478 (coe v1)) (coe d_halted_480 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
d_writeLocToHeap_696 ~v0 v1 v2 v3 = du_writeLocToHeap_696 v1 v2 v3
du_writeLocToHeap_696 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
du_writeLocToHeap_696 v0 v1 v2
  = coe
      C_mkLocState_482 (coe d_regs_474 (coe v0))
      (coe d_stackMem_476 (coe v0))
      (coe
         du_writeHeapMem_676 (coe d_heapMem_478 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_480 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_462
d_writeLoc_704 v0 v1 v2 v3
  = case coe v2 of
      C_AtStack_72 v4 v5
        -> coe
             d_writeLocToStack_686 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      C_AtDynamic_74 v4
        -> case coe v3 of
             C_SV'45'Ptr_82 v5
               -> case coe v5 of
                    C_AtStack_72 v6 v7 -> coe v1
                    C_AtDynamic_74 v6
                      -> coe du_writeLocToHeap_696 (coe v1) (coe v4) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Tag_84 v5
               -> coe du_writeLocToHeap_696 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_88 v5 v6 v7
               -> coe du_writeLocToHeap_696 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_90 v5
               -> coe du_writeLocToHeap_696 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_750 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_788 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_828 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_828 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_848 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_848 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_876 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_908 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1148 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1200 a0 = ()
data T_LocSourceExt_1200
  = C_Loc_1204 T_ValueLocation_68 | C_IndReg_1206 T_AbstractReg_56 |
    C_IndRegSuc_1208 T_AbstractReg_56
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_78 -> Maybe T_ValueLocation_68
d_sv'45'as'45'loc_1212 ~v0 v1 = du_sv'45'as'45'loc_1212 v1
du_sv'45'as'45'loc_1212 ::
  T_StoredValue_78 -> Maybe T_ValueLocation_68
du_sv'45'as'45'loc_1212 v0
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
d_resolveSourceExt_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_136 -> T_LocSourceExt_1200 -> Maybe T_ValueLocation_68
d_resolveSourceExt_1218 ~v0 v1 v2 = du_resolveSourceExt_1218 v1 v2
du_resolveSourceExt_1218 ::
  T_Registers_136 -> T_LocSourceExt_1200 -> Maybe T_ValueLocation_68
du_resolveSourceExt_1218 v0 v1
  = case coe v1 of
      C_Loc_1204 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1206 v2
        -> coe
             du_sv'45'as'45'loc_1212 (coe du_readReg_164 (coe v0) (coe v2))
      C_IndRegSuc_1208 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1212 (coe du_readReg_164 (coe v0) (coe v2)) in
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
d_Instr_1248 a0 = ()
data T_Instr_1248
  = C_load_1252 T_AbstractReg_56 T_LocSourceExt_1200 |
    C_store_1254 T_LocSourceExt_1200 T_AbstractReg_56 |
    C_mov_1256 T_AbstractReg_56 T_AbstractReg_56
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1264 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_1264 v0 v1 = coe d_heapMem_478 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_1266 ~v0 = du_readLoc_1266
du_readLoc_1266 ::
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_1266 = coe du_readLoc_624
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1268 ::
  T_LocState_462 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_1268 v0 v1 v2 = coe d_stackMem_476 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_1270 ~v0 = du_writeHeapMem_1270
du_writeHeapMem_1270 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_1270 = coe du_writeHeapMem_676
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_1272 ~v0 = du_writeHeapMem'45'aux_1272
du_writeHeapMem'45'aux_1272 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_1272 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_670 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_462
d_writeLoc_1274 v0 = coe d_writeLoc_704 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1276 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1278 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1278 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1280 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1282 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1284 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1286 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1288 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1288 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
d_writeLocToHeap_1290 ~v0 = du_writeLocToHeap_1290
du_writeLocToHeap_1290 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
du_writeLocToHeap_1290 = coe du_writeLocToHeap_696
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_462
d_writeLocToStack_1292 v0 = coe d_writeLocToStack_686 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_1294 v0 = coe d_writeStackMem_652 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_1296 ~v0 = du_writeStackMem'45'aux_1296
du_writeStackMem'45'aux_1296 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_1296 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_644 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'with'45'value_1298 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1298 v1 v2
du_exec'45'load'45'with'45'value_1298 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'with'45'value_1298 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_482 (coe du_writeReg_176 (d_regs_474 (coe v3)) v0 v2)
                  (coe d_stackMem_476 (coe v3)) (coe d_heapMem_478 (coe v3))
                  (coe d_halted_480 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_482 (coe d_regs_474 (coe v2))
                  (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'via'45'resolved_1310 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1310 v1 v2
du_exec'45'load'45'via'45'resolved_1310 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'via'45'resolved_1310 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1298 v0
                  (coe du_readLoc_624 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_482 (coe d_regs_474 (coe v2))
                  (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'store'45'via'45'resolved_1322 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_704 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_482 (coe d_regs_474 (coe v3))
                  (coe d_stackMem_476 (coe v3)) (coe d_heapMem_478 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'suc'45'via'45'resolved_1332 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1332 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1332 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'suc'45'via'45'resolved_1332 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1298 v0
                  (coe du_readLoc_624 (coe v3) (coe du_sucLoc_94 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_482 (coe d_regs_474 (coe v2))
                  (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'store'45'suc'45'via'45'resolved_1344 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_704
                  (coe v0) (coe v4) (coe du_sucLoc_94 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_482 (coe d_regs_474 (coe v3))
                  (coe d_stackMem_476 (coe v3)) (coe d_heapMem_478 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1248 -> T_LocState_462 -> T_LocState_462
d_exec_1354 v0 v1
  = case coe v1 of
      C_load_1252 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1310 v2
                  (coe du_resolveSourceExt_1218 (coe d_regs_474 (coe v4)) (coe v3))
                  v4)
      C_store_1254 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1322 v0
                  (coe du_resolveSourceExt_1218 (coe d_regs_474 (coe v4)) (coe v2))
                  (coe du_readReg_164 (coe d_regs_474 (coe v4)) (coe v3)) v4)
      C_mov_1256 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_482
                  (coe
                     du_writeReg_176 (d_regs_474 (coe v4)) v2
                     (coe du_readReg_164 (coe d_regs_474 (coe v4)) (coe v3)))
                  (coe d_stackMem_476 (coe v4)) (coe d_heapMem_478 (coe v4))
                  (coe d_halted_480 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1380 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1386 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1248] -> T_LocState_462 -> T_LocState_462
d_execList_1388 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_480 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1388 (coe v0) (coe v4) (coe d_exec_1354 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1420 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_1420 v0 v1 = coe d_heapMem_478 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_1422 ~v0 = du_readLoc_1422
du_readLoc_1422 ::
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_1422 = coe du_readLoc_624
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1424 ::
  T_LocState_462 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_1424 v0 v1 v2 = coe d_stackMem_476 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_1426 ~v0 = du_writeHeapMem_1426
du_writeHeapMem_1426 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_1426 = coe du_writeHeapMem_676
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_1428 ~v0 = du_writeHeapMem'45'aux_1428
du_writeHeapMem'45'aux_1428 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_1428 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_670 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_462
d_writeLoc_1430 v0 = coe d_writeLoc_704 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1432 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1434 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1434 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1436 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1438 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1440 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1442 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1444 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1444 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
d_writeLocToHeap_1446 ~v0 = du_writeLocToHeap_1446
du_writeLocToHeap_1446 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
du_writeLocToHeap_1446 = coe du_writeLocToHeap_696
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_462
d_writeLocToStack_1448 v0 = coe d_writeLocToStack_686 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_1450 v0 = coe d_writeStackMem_652 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_1452 ~v0 = du_writeStackMem'45'aux_1452
du_writeStackMem'45'aux_1452 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_1452 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_644 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1248 -> T_LocState_462 -> T_LocState_462
d_exec_1456 v0 = coe d_exec_1354 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1458 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1460 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'suc'45'via'45'resolved_1462 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1462
du_exec'45'load'45'suc'45'via'45'resolved_1462 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'suc'45'via'45'resolved_1462
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1332
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'via'45'resolved_1464 ~v0
  = du_exec'45'load'45'via'45'resolved_1464
du_exec'45'load'45'via'45'resolved_1464 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'via'45'resolved_1464
  = coe du_exec'45'load'45'via'45'resolved_1310
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'with'45'value_1466 ~v0
  = du_exec'45'load'45'with'45'value_1466
du_exec'45'load'45'with'45'value_1466 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'with'45'value_1466
  = coe du_exec'45'load'45'with'45'value_1298
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'store'45'suc'45'via'45'resolved_1468 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1344 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'store'45'via'45'resolved_1470 v0
  = coe d_exec'45'store'45'via'45'resolved_1322 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1472 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1248] -> T_LocState_462 -> T_LocState_462
d_execList_1472 v0 = coe d_execList_1388 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_LocSourceExt_1200 -> Maybe T_StoredValue_78
d_resolved'45'readLoc_1474 ~v0 v1 v2
  = du_resolved'45'readLoc_1474 v1 v2
du_resolved'45'readLoc_1474 ::
  T_LocState_462 -> T_LocSourceExt_1200 -> Maybe T_StoredValue_78
du_resolved'45'readLoc_1474 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1218 (coe d_regs_474 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_624 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1504 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1574 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_LocState_462 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1650 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1680 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1736 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1788 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1840 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 ->
  T_AbstractReg_56 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1856 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1874 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1874 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1888 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1906 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_1972 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_1972 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_1996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_1996 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2024 = ()
data T_FlatCtrl_2024
  = C_c'45'label_2026 Integer | C_c'45'jmp_2028 Integer |
    C_c'45'branch'45'scratch'45'zero_2030 Integer |
    C_c'45'branch'45'tag'45'zero_2032 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2034 = ()
data T_AbstractInstr_2034
  = C_mov'45'to'45'output_2036 | C_mov'45'to'45'input_2038 |
    C_mov'45'output'45'to'45'input2_2040 |
    C_mov'45'input2'45'to'45'output_2042 | C_load'45'indirect_2044 |
    C_load'45'indirect'45'suc_2046 |
    C_load'45'from'45'slot_2048 Integer |
    C_store'45'at'45'slot_2050 Integer | C_store'45'indirect_2052 |
    C_store'45'indirect'45'suc_2054 | C_lea'45'slot_2056 Integer |
    C_restore'45'input_2058 Integer |
    C_instr'45'alloc'45'stack_2060 Integer |
    C_instr'45'dealloc'45'stack_2062 Integer |
    C_instr'45'reclaim'45'to_2064 Integer |
    C_instr'45'push'45'frame_2066 Integer |
    C_instr'45'pop'45'frame_2068 | C_instr'45'call'45'closure_2070 |
    C_worklist'45'init_2072 Integer | C_worklist'45'push_2074 Integer |
    C_worklist'45'pop_2076 Integer | C_worklist'45'check_2078 Integer |
    C_instr'45'sigop_2084 MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.Type.T_Type_108
                          MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 |
    C_instr'45'load'45'const_2088 MAlonzo.Code.Once.Type.T_Type_108
                                  MAlonzo.Code.Once.Type.T_FitsInReg_188 AgdaAny |
    C_instr'45'load'45'code'45'addr_2090 Integer |
    C_instr'45'save'45'closure'45'reg_2092 |
    C_instr'45'load'45'tag'45'lit_2094 Integer |
    C_instr'45'case'45'on'45'tag_2096 [T_AbstractInstr_2034]
                                      [T_AbstractInstr_2034] |
    C_instr'45'alloc'45'heap_2098 Integer |
    C_instr'45'loop_2100 [T_AbstractInstr_2034] |
    C_instr'45'reg'45'op_2102 T_RegOp_434 |
    C_instr'45'ctrl_2104 T_FlatCtrl_2024
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2106 :: ()
d_AbstractTrace_2106 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2108 = ()
data T_TreeTrace_2108
  = C_ε_2110 | C_instr_2112 T_AbstractInstr_2034 |
    C__'9656'__2114 T_TreeTrace_2108 T_TreeTrace_2108 |
    C_branch_2116 Integer T_TreeTrace_2108 T_TreeTrace_2108 |
    C_call'45'sub_2118 T_TreeTrace_2108 |
    C_flat_2120 [T_AbstractInstr_2034]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2122 :: [T_AbstractInstr_2034] -> T_TreeTrace_2108
d_flatToTree_2122 v0
  = case coe v0 of
      [] -> coe C_ε_2110
      (:) v1 v2
        -> coe
             C__'9656'__2114 (coe C_instr_2112 (coe v1))
             (coe d_flatToTree_2122 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2128 :: T_TreeTrace_2108 -> [T_AbstractInstr_2034]
d_treeToFlat_2128 v0
  = case coe v0 of
      C_ε_2110 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2112 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2114 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2128 (coe v1)) (coe d_treeToFlat_2128 (coe v2))
      C_branch_2116 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2128 (coe v2)) (coe d_treeToFlat_2128 (coe v3))
      C_call'45'sub_2118 v1 -> coe d_treeToFlat_2128 (coe v1)
      C_flat_2120 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2144 ::
  Integer -> T_TreeTrace_2108 -> [T_AbstractInstr_2034]
d_treeToRunnable_2144 v0 v1
  = case coe v1 of
      C_ε_2110 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2112 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2114 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2144 (coe v0) (coe v2))
             (coe d_treeToRunnable_2144 (coe v0) (coe v3))
      C_branch_2116 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2144 (coe v0) (coe v3))
             (coe d_treeToRunnable_2144 (coe v0) (coe v4))
      C_call'45'sub_2118 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2074 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2144 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2076 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2120 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2174 ::
  Integer -> T_TreeTrace_2108 -> [T_AbstractInstr_2034]
d_treeToRunnableWithInit_2174 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2072 (coe v0))
      (coe d_treeToRunnable_2144 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2210 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_readHeapLoc_2210 v0 v1 = coe d_heapMem_478 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
d_readLoc_2212 ~v0 = du_readLoc_2212
du_readLoc_2212 ::
  T_LocState_462 -> T_ValueLocation_68 -> Maybe T_StoredValue_78
du_readLoc_2212 = coe du_readLoc_624
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2214 ::
  T_LocState_462 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_readStackLoc_2214 v0 v1 v2 = coe d_stackMem_476 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
d_writeHeapMem_2216 ~v0 = du_writeHeapMem_2216
du_writeHeapMem_2216 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_78) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_78
du_writeHeapMem_2216 = coe du_writeHeapMem_676
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeHeapMem'45'aux_2218 ~v0 = du_writeHeapMem'45'aux_2218
du_writeHeapMem'45'aux_2218 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeHeapMem'45'aux_2218 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_670 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 -> T_StoredValue_78 -> T_LocState_462
d_writeLoc_2220 v0 = coe d_writeLoc_704 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2222 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2224 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2224 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2226 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2228 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2230 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2232 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2234 ::
  T_LocState_462 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 ->
  T_Registers_136 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2234 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
d_writeLocToHeap_2236 ~v0 = du_writeLocToHeap_2236
du_writeLocToHeap_2236 ::
  T_LocState_462 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_78 -> T_LocState_462
du_writeLocToHeap_2236 = coe du_writeLocToHeap_696
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  AgdaAny -> Integer -> T_StoredValue_78 -> T_LocState_462
d_writeLocToStack_2238 v0 = coe d_writeLocToStack_686 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_78) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_78 -> AgdaAny -> Integer -> Maybe T_StoredValue_78
d_writeStackMem_2240 v0 = coe d_writeStackMem_652 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
d_writeStackMem'45'aux_2242 ~v0 = du_writeStackMem'45'aux_2242
du_writeStackMem'45'aux_2242 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_78 ->
  T_StoredValue_78 -> Maybe T_StoredValue_78
du_writeStackMem'45'aux_2242 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_644 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1248 -> T_LocState_462 -> T_LocState_462
d_exec_2246 v0 = coe d_exec_1354 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2248 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2250 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'suc'45'via'45'resolved_2252 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2252
du_exec'45'load'45'suc'45'via'45'resolved_2252 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'suc'45'via'45'resolved_2252
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1332
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'via'45'resolved_2254 ~v0
  = du_exec'45'load'45'via'45'resolved_2254
du_exec'45'load'45'via'45'resolved_2254 ::
  T_AbstractReg_56 ->
  Maybe T_ValueLocation_68 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'via'45'resolved_2254
  = coe du_exec'45'load'45'via'45'resolved_1310
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'load'45'with'45'value_2256 ~v0
  = du_exec'45'load'45'with'45'value_2256
du_exec'45'load'45'with'45'value_2256 ::
  T_AbstractReg_56 ->
  Maybe T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
du_exec'45'load'45'with'45'value_2256
  = coe du_exec'45'load'45'with'45'value_1298
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'store'45'suc'45'via'45'resolved_2258 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1344 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_ValueLocation_68 ->
  T_StoredValue_78 -> T_LocState_462 -> T_LocState_462
d_exec'45'store'45'via'45'resolved_2260 v0
  = coe d_exec'45'store'45'via'45'resolved_1322 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1248] -> T_LocState_462 -> T_LocState_462
d_execList_2262 v0 = coe d_execList_1388 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2266 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_LocState_462 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2268 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2270 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2272 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2274 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_AbstractReg_56 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2276 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2278 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_LocSourceExt_1200 ->
  T_ValueLocation_68 ->
  T_LocState_462 ->
  T_StoredValue_78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2280 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2282 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 ->
  T_AbstractReg_56 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2284 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2286 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_56 ->
  T_AbstractReg_56 ->
  T_LocState_462 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2288 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 ->
  T_LocState_462 ->
  T_ValueLocation_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2290 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_LocSourceExt_1200 -> Maybe T_StoredValue_78
d_resolved'45'readLoc_2292 ~v0 = du_resolved'45'readLoc_2292
du_resolved'45'readLoc_2292 ::
  T_LocState_462 -> T_LocSourceExt_1200 -> Maybe T_StoredValue_78
du_resolved'45'readLoc_2292 = coe du_resolved'45'readLoc_1474
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2294 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2294 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2294 ::
  Maybe T_StoredValue_78 ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2294 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe du_writeReg_176 (d_regs_474 (coe v1)) (coe C_Output_62) v3)
                (coe d_stackMem_476 (coe v1)) (coe d_heapMem_478 (coe v1))
                (coe d_halted_480 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482 (coe d_regs_474 (coe v1))
                (coe d_stackMem_476 (coe v1)) (coe d_heapMem_478 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2306 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2306 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2306 ::
  Maybe T_StoredValue_78 ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2306 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe du_writeReg_176 (d_regs_474 (coe v1)) (coe C_Input1_58) v3)
                (coe d_stackMem_476 (coe v1)) (coe d_heapMem_478 (coe v1))
                (coe d_halted_480 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482 (coe d_regs_474 (coe v1))
                (coe d_stackMem_476 (coe v1)) (coe d_heapMem_478 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2324 ::
  T_StoredValue_78 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2324 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2330 ::
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2330 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2338 ::
  T_StoredValue_78 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2338 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2344 ::
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2344 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_78
d_unit'45'storedvalue_2346 ~v0 = du_unit'45'storedvalue_2346
du_unit'45'storedvalue_2346 :: T_StoredValue_78
du_unit'45'storedvalue_2346
  = coe
      C_SV'45'Lit_88 (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_190) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2352
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_462 -> T_StoredValue_78
d_pure'45'sigop'45'output_2358 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_196 (coe v2) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
           -> coe du_unit'45'storedvalue_2346
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe d_structured'45'pure'45'sigop'45'output_2352 v0 v1 v2 v3 v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_262 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_462 -> T_StoredValue_78
d_exec'45'sigop'45'output'45'of_2392 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_266
        -> coe
             d_pure'45'sigop'45'output_2358 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Emits_268
        -> coe du_unit'45'storedvalue_2346
      MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_270
        -> coe du_unit'45'storedvalue_2346
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_462 -> T_StoredValue_78
d_exec'45'sigop'45'output_2402 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2392 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_296 (coe v3))
      (coe v3) (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_262 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_462 -> Bool
d_exec'45'sigop'45'halts'45'of_2412 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2412 v3
du_exec'45'sigop'45'halts'45'of_2412 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_EffectShape_262 -> Bool
du_exec'45'sigop'45'halts'45'of_2412 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_270
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 ->
  T_LocState_462 -> Bool
d_exec'45'sigop'45'halts_2418 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2418 v3
du_exec'45'sigop'45'halts_2418 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_276 -> Bool
du_exec'45'sigop'45'halts_2418 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2412
      (coe MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_296 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> Maybe T_StoredValue_78
d_case'45'tag'45'at_2424 ~v0 v1 = du_case'45'tag'45'at_2424 v1
du_case'45'tag'45'at_2424 ::
  T_LocState_462 -> Maybe T_StoredValue_78
du_case'45'tag'45'at_2424 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1212
              (coe d_input1_150 (coe d_regs_474 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_624 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2034 ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2438 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2036
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Input1_58)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2038
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Input1_58)
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Output_62)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_2040
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Input2_60)
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Output_62)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_2042
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Input2_60)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_load'45'indirect_2044
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1310 (coe C_Output_62)
                (coe
                   du_sv'45'as'45'loc_1212
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Input1_58)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2046
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1332 (coe C_Output_62)
                (coe
                   du_sv'45'as'45'loc_1212
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Input1_58)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2048 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2294
             (coe
                du_readLoc_624 (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_574 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2050 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_704 (coe v0) (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_574 (coe v3)) (coe v4))
                (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Output_62)))
             (coe v3)
      C_store'45'indirect_2052
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1322 v0
                (coe
                   du_sv'45'as'45'loc_1212
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Input1_58)))
                (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Output_62))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2054
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1344 v0
                (coe
                   du_sv'45'as'45'loc_1212
                   (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Input1_58)))
                (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Output_62))
                v2)
             (coe v3)
      C_lea'45'slot_2056 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe
                      C_SV'45'Ptr_82
                      (coe C_AtStack_72 (coe d_current'45'frame_574 (coe v3)) (coe v4))))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_restore'45'input_2058 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2306
             (coe
                du_readLoc_624 (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_574 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2060 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe du_incrStackSlot_204 (coe d_regs_474 (coe v2)) (coe v4))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe
                C_mkAllocState_580 (coe d_current'45'frame_574 (coe v3))
                (coe addInt (coe d_next'45'slot_576 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_578 (coe v3)))
      C_instr'45'dealloc'45'stack_2062 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe du_decrStackSlot_212 (coe d_regs_474 (coe v2)) (coe v4))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_2064 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_580 (coe d_current'45'frame_574 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_578 (coe v3)))
      C_instr'45'push'45'frame_2066 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeStackSlot_196 (coe d_regs_474 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_2068
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2070
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2072 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2074 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_704 (coe v0) (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_574 (coe v3)) (coe v4))
                (coe du_readReg_164 (coe d_regs_474 (coe v2)) (coe C_Output_62)))
             (coe v3)
      C_worklist'45'pop_2076 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2294
             (coe
                du_readLoc_624 (coe v2)
                (coe C_AtStack_72 (coe d_current'45'frame_574 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2078 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2084 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (d_exec'45'sigop'45'output_2402
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe du_exec'45'sigop'45'halts_2418 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2088 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Lit_88 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2090 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Code_90 (coe v4)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2092
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2094 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe C_SV'45'Tag_84 (coe v4)))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2096 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2444 (coe v0)
             (coe du_case'45'tag'45'at_2424 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2098 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482
                (coe
                   du_writeReg_176 (d_regs_474 (coe v2)) (coe C_Output_62)
                   (coe
                      C_SV'45'Ptr_82
                      (coe
                         C_AtDynamic_74
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_578 (coe v3)))))))
                (coe d_stackMem_476 (coe v2)) (coe d_heapMem_478 (coe v2))
                (coe d_halted_480 (coe v2)))
             (coe
                C_mkAllocState_580 (coe d_current'45'frame_574 (coe v3))
                (coe d_next'45'slot_576 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_578 (coe v3))))))
      C_instr'45'loop_2100 v4
        -> coe
             d_exec'45'loop_2442 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2102 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_502 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2104 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2440 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2034] ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2440 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_480 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2440 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2438 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2438 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2034] ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2442 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482 (coe d_regs_474 (coe v3))
                (coe d_stackMem_476 (coe v3)) (coe d_heapMem_478 (coe v3))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v4)
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6 = d_halted_480 (coe v3) in
              coe
                (if coe v6
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4)
                   else (let v7 = d_scratch_158 (coe d_regs_474 (coe v3)) in
                         coe
                           (let v8
                                  = d_exec'45'loop_2442
                                      (coe v0) (coe v5) (coe v2)
                                      (coe
                                         C_mkLocState_482
                                         (coe
                                            d_regs_474
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2440 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe d_stackMem_476 (coe v3))
                                         (coe
                                            d_heapMem_478
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2440 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe
                                            d_halted_480
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2440 (coe v0) (coe v2) (coe v3)
                                                  (coe v4)))))
                                      (coe
                                         C_mkAllocState_580 (coe d_current'45'frame_574 (coe v4))
                                         (coe d_next'45'slot_576 (coe v4))
                                         (coe
                                            d_next'45'heap'45'ref_578
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_exec'45'trace_2440 (coe v0) (coe v2) (coe v3)
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
d_exec'45'case'45'dispatch_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_78 ->
  [T_AbstractInstr_2034] ->
  [T_AbstractInstr_2034] ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2444 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_82 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_482 (coe d_regs_474 (coe v4))
                       (coe d_stackMem_476 (coe v4)) (coe d_heapMem_478 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Tag_84 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_2440 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2440 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_88 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_482 (coe d_regs_474 (coe v4))
                       (coe d_stackMem_476 (coe v4)) (coe d_heapMem_478 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Code_90 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_482 (coe d_regs_474 (coe v4))
                       (coe d_stackMem_476 (coe v4)) (coe d_heapMem_478 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_482 (coe d_regs_474 (coe v4))
                (coe d_stackMem_476 (coe v4)) (coe d_heapMem_478 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2034 ->
  [T_AbstractInstr_2034] ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2780 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2034 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2826 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_2860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_462 -> T_AllocState_516 -> Integer -> Maybe Integer
d_getTag_2860 ~v0 v1 v2 v3 = du_getTag_2860 v1 v2 v3
du_getTag_2860 ::
  T_LocState_462 -> T_AllocState_516 -> Integer -> Maybe Integer
du_getTag_2860 v0 v1 v2
  = let v3
          = coe d_stackMem_476 v0 (d_current'45'frame_574 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_2884 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2108 ->
  T_LocState_462 ->
  T_AllocState_516 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_2884 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2110
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2112 v4
        -> let v5 = d_halted_480 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2438 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2114 v4 v5
        -> let v6 = d_halted_480 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2884 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_2884 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_2884 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2116 v4 v5 v6
        -> let v7 = d_halted_480 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_476 v2 (d_current'45'frame_574 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_2884 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_2884 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_2884 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_2884 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_2884 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2118 v4
        -> let v5 = d_halted_480 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_2884 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2120 v4
        -> coe d_exec'45'trace_2440 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3044 ::
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3044 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2108 ->
  T_TreeTrace_2108 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3062 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2034 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3108 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2108 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3148 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2034] ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3188 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2034] ->
  [T_AbstractInstr_2034] ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3208 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3266
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2108 ->
  T_LocState_462 ->
  T_AllocState_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3274 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3274
du_exec'45'tree'45'flat'45'equiv'45'simple_3274 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3274
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
