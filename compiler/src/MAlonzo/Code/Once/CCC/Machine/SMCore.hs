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
  = C_Input1_56 | C_Input2_58 | C_Output_60 | C_Scratch_62
-- Once.CCC.Machine.SMCore.StoredValue
d_StoredValue_66 a0 = ()
data T_StoredValue_66
  = C_SV'45'Ptr_70 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_SV'45'Tag_72 Integer |
    C_SV'45'Lit_76 MAlonzo.Code.Once.Type.T_Type_112
                   MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_SV'45'Code_78 Integer
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
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers
d_Registers_124 a0 = ()
data T_Registers_124
  = C_mkRegs_148 T_StoredValue_66 T_StoredValue_66 T_StoredValue_66
                 Integer T_StoredValue_66
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_138 :: T_Registers_124 -> T_StoredValue_66
d_input1_138 v0
  = case coe v0 of
      C_mkRegs_148 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.input2
d_input2_140 :: T_Registers_124 -> T_StoredValue_66
d_input2_140 v0
  = case coe v0 of
      C_mkRegs_148 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_142 :: T_Registers_124 -> T_StoredValue_66
d_output_142 v0
  = case coe v0 of
      C_mkRegs_148 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.stackSlot
d_stackSlot_144 :: T_Registers_124 -> Integer
d_stackSlot_144 v0
  = case coe v0 of
      C_mkRegs_148 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.scratch
d_scratch_146 :: T_Registers_124 -> T_StoredValue_66
d_scratch_146 v0
  = case coe v0 of
      C_mkRegs_148 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 -> T_AbstractReg_54 -> T_StoredValue_66
d_readReg_152 ~v0 v1 v2 = du_readReg_152 v1 v2
du_readReg_152 ::
  T_Registers_124 -> T_AbstractReg_54 -> T_StoredValue_66
du_readReg_152 v0 v1
  = case coe v1 of
      C_Input1_56 -> coe d_input1_138 (coe v0)
      C_Input2_58 -> coe d_input2_140 (coe v0)
      C_Output_60 -> coe d_output_142 (coe v0)
      C_Scratch_62 -> coe d_scratch_146 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 -> T_StoredValue_66 -> T_Registers_124
d_writeReg_164 ~v0 v1 v2 = du_writeReg_164 v1 v2
du_writeReg_164 ::
  T_Registers_124 ->
  T_AbstractReg_54 -> T_StoredValue_66 -> T_Registers_124
du_writeReg_164 v0 v1
  = case coe v1 of
      C_Input1_56
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_148 (coe v2) (coe d_input2_140 (coe v0))
                  (coe d_output_142 (coe v0)) (coe d_stackSlot_144 (coe v0))
                  (coe d_scratch_146 (coe v0)))
      C_Input2_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_148 (coe d_input1_138 (coe v0)) (coe v2)
                  (coe d_output_142 (coe v0)) (coe d_stackSlot_144 (coe v0))
                  (coe d_scratch_146 (coe v0)))
      C_Output_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_148 (coe d_input1_138 (coe v0))
                  (coe d_input2_140 (coe v0)) (coe v2) (coe d_stackSlot_144 (coe v0))
                  (coe d_scratch_146 (coe v0)))
      C_Scratch_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_148 (coe d_input1_138 (coe v0))
                  (coe d_input2_140 (coe v0)) (coe d_output_142 (coe v0))
                  (coe d_stackSlot_144 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeStackSlot
d_writeStackSlot_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 -> Integer -> T_Registers_124
d_writeStackSlot_184 ~v0 v1 v2 = du_writeStackSlot_184 v1 v2
du_writeStackSlot_184 ::
  T_Registers_124 -> Integer -> T_Registers_124
du_writeStackSlot_184 v0 v1
  = coe
      C_mkRegs_148 (coe d_input1_138 (coe v0))
      (coe d_input2_140 (coe v0)) (coe d_output_142 (coe v0)) (coe v1)
      (coe d_scratch_146 (coe v0))
-- Once.CCC.Machine.SMCore.incrStackSlot
d_incrStackSlot_192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 -> Integer -> T_Registers_124
d_incrStackSlot_192 ~v0 v1 v2 = du_incrStackSlot_192 v1 v2
du_incrStackSlot_192 ::
  T_Registers_124 -> Integer -> T_Registers_124
du_incrStackSlot_192 v0 v1
  = coe
      C_mkRegs_148 (coe d_input1_138 (coe v0))
      (coe d_input2_140 (coe v0)) (coe d_output_142 (coe v0))
      (coe addInt (coe d_stackSlot_144 (coe v0)) (coe v1))
      (coe d_scratch_146 (coe v0))
-- Once.CCC.Machine.SMCore.decrStackSlot
d_decrStackSlot_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 -> Integer -> T_Registers_124
d_decrStackSlot_200 ~v0 v1 v2 = du_decrStackSlot_200 v1 v2
du_decrStackSlot_200 ::
  T_Registers_124 -> Integer -> T_Registers_124
du_decrStackSlot_200 v0 v1
  = coe
      C_mkRegs_148 (coe d_input1_138 (coe v0))
      (coe d_input2_140 (coe v0)) (coe d_output_142 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (d_stackSlot_144 (coe v0)) v1)
      (coe d_scratch_146 (coe v0))
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_220 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_342 = erased
-- Once.CCC.Machine.SMCore.writeReg-preserves-stackSlot
d_writeReg'45'preserves'45'stackSlot_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves'45'stackSlot_368 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_396 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_422 = ()
data T_RegOp_422
  = C_scratch'45'one_424 | C_scratch'45'zero_426 |
    C_scratch'45'dec_428 | C_scratch'45'load'45'count_430 |
    C_input2'45'zero_432 | C_input2'45'inc_434
-- Once.CCC.Machine.SMCore.sv-succ
d_sv'45'succ_438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'succ_438 ~v0 v1 = du_sv'45'succ_438 v1
du_sv'45'succ_438 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'succ_438 v0
  = let v1 = coe C_SV'45'Tag_72 (coe (1 :: Integer)) in
    coe
      (case coe v0 of
         C_SV'45'Tag_72 v2
           -> coe C_SV'45'Tag_72 (coe addInt (coe (1 :: Integer)) (coe v2))
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.sv-pred
d_sv'45'pred_444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'pred_444 ~v0 v1 = du_sv'45'pred_444 v1
du_sv'45'pred_444 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'pred_444 v0
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
d_sv'45'tag'45'val_450 :: T_StoredValue_66 -> Integer
d_sv'45'tag'45'val_450 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         C_SV'45'Tag_72 v2 -> coe v2
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.LocState
d_LocState_456 a0 = ()
data T_LocState_456
  = C_mkLocState_476 T_Registers_124
                     (AgdaAny -> Integer -> Maybe T_StoredValue_66)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                      Maybe T_StoredValue_66)
                     Bool
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_468 :: T_LocState_456 -> T_Registers_124
d_regs_468 v0
  = case coe v0 of
      C_mkLocState_476 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_470 ::
  T_LocState_456 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_stackMem_470 v0
  = case coe v0 of
      C_mkLocState_476 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_472 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_heapMem_472 v0
  = case coe v0 of
      C_mkLocState_476 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_474 :: T_LocState_456 -> Bool
d_halted_474 v0
  = case coe v0 of
      C_mkLocState_476 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_422 -> T_Registers_124 -> T_Registers_124
d_setReg_480 ~v0 v1 v2 = du_setReg_480 v1 v2
du_setReg_480 :: T_RegOp_422 -> T_Registers_124 -> T_Registers_124
du_setReg_480 v0 v1
  = case coe v0 of
      C_scratch'45'one_424
        -> coe
             du_writeReg_164 v1 (coe C_Scratch_62)
             (coe C_SV'45'Tag_72 (coe (1 :: Integer)))
      C_scratch'45'zero_426
        -> coe
             du_writeReg_164 v1 (coe C_Scratch_62)
             (coe C_SV'45'Tag_72 (coe (0 :: Integer)))
      C_scratch'45'dec_428
        -> coe
             du_writeReg_164 v1 (coe C_Scratch_62)
             (coe
                du_sv'45'pred_444 (coe du_readReg_152 (coe v1) (coe C_Scratch_62)))
      C_scratch'45'load'45'count_430
        -> coe
             du_writeReg_164 v1 (coe C_Scratch_62)
             (coe du_readReg_152 (coe v1) (coe C_Input2_58))
      C_input2'45'zero_432
        -> coe
             du_writeReg_164 v1 (coe C_Input2_58)
             (coe C_SV'45'Tag_72 (coe (0 :: Integer)))
      C_input2'45'inc_434
        -> coe
             du_writeReg_164 v1 (coe C_Input2_58)
             (coe
                du_sv'45'succ_438 (coe du_readReg_152 (coe v1) (coe C_Input2_58)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_422 -> T_LocState_456 -> T_LocState_456
d_exec'45'reg'45'op_496 ~v0 v1 v2 = du_exec'45'reg'45'op_496 v1 v2
du_exec'45'reg'45'op_496 ::
  T_RegOp_422 -> T_LocState_456 -> T_LocState_456
du_exec'45'reg'45'op_496 v0 v1
  = coe
      C_mkLocState_476
      (coe du_setReg_480 (coe v0) (coe d_regs_468 (coe v1)))
      (coe d_stackMem_470 (coe v1)) (coe d_heapMem_472 (coe v1))
      (coe d_halted_474 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_502 = ()
data T_AllocMode_502 = C_Stack_504 | C_Heap_506
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_510 a0 = ()
data T_AllocState_510
  = C_mkAllocState_594 AgdaAny [AgdaAny] Integer Integer
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_586 :: T_AllocState_510 -> AgdaAny
d_current'45'frame_586 v0
  = case coe v0 of
      C_mkAllocState_594 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_588 :: T_AllocState_510 -> [AgdaAny]
d_saved'45'frames_588 v0
  = case coe v0 of
      C_mkAllocState_594 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_590 :: T_AllocState_510 -> Integer
d_next'45'slot_590 v0
  = case coe v0 of
      C_mkAllocState_594 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_592 :: T_AllocState_510 -> Integer
d_next'45'heap'45'ref_592 v0
  = case coe v0 of
      C_mkAllocState_594 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_632 ::
  T_LocState_456 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_632 v0 v1 v2 = coe d_stackMem_470 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_640 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_640 v0 v1 = coe d_heapMem_472 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_646 ~v0 v1 v2 = du_readLoc_646 v1 v2
du_readLoc_646 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_646 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_470 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_472 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_666 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_666 v5 v6 v7 v8
du_writeStackMem'45'aux_666 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_666 v0 v1 v2 v3
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
d_writeStackMem_674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_674 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_666
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__84 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_692 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_692 v3 v4 v5
du_writeHeapMem'45'aux_692 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_692 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_698 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_698 v1 v2 v3 v4
du_writeHeapMem_698 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_698 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_692
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__80 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_456
d_writeLocToStack_708 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_476 (coe d_regs_468 (coe v1))
      (coe
         d_writeStackMem_674 (coe v0) (coe d_stackMem_470 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_472 (coe v1)) (coe d_halted_474 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLocToHeap_718 ~v0 v1 v2 v3 = du_writeLocToHeap_718 v1 v2 v3
du_writeLocToHeap_718 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
du_writeLocToHeap_718 v0 v1 v2
  = coe
      C_mkLocState_476 (coe d_regs_468 (coe v0))
      (coe d_stackMem_470 (coe v0))
      (coe
         du_writeHeapMem_698 (coe d_heapMem_472 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_474 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLoc_726 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_708 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_70 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
                      -> coe v1
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
                      -> coe du_writeLocToHeap_718 (coe v1) (coe v4) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Tag_72 v5
               -> coe du_writeLocToHeap_718 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_76 v5 v6 v7
               -> coe du_writeLocToHeap_718 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_78 v5
               -> coe du_writeLocToHeap_718 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_772 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_810 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_850 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_850 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_870 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_870 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_898 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_930 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1170 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1222 a0 = ()
data T_LocSourceExt_1222
  = C_Loc_1226 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1228 T_AbstractReg_54 | C_IndRegSuc_1230 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1234 ~v0 v1 = du_sv'45'as'45'loc_1234 v1
du_sv'45'as'45'loc_1234 ::
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1234 v0
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
d_resolveSourceExt_1240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_124 ->
  T_LocSourceExt_1222 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1240 ~v0 v1 v2 = du_resolveSourceExt_1240 v1 v2
du_resolveSourceExt_1240 ::
  T_Registers_124 ->
  T_LocSourceExt_1222 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1240 v0 v1
  = case coe v1 of
      C_Loc_1226 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1228 v2
        -> coe
             du_sv'45'as'45'loc_1234 (coe du_readReg_152 (coe v0) (coe v2))
      C_IndRegSuc_1230 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1234 (coe du_readReg_152 (coe v0) (coe v2)) in
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
d_Instr_1270 a0 = ()
data T_Instr_1270
  = C_load_1274 T_AbstractReg_54 T_LocSourceExt_1222 |
    C_store_1276 T_LocSourceExt_1222 T_AbstractReg_54 |
    C_mov_1278 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1286 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1286 v0 v1 = coe d_heapMem_472 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1288 ~v0 = du_readLoc_1288
du_readLoc_1288 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1288 = coe du_readLoc_646
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1290 ::
  T_LocState_456 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1290 v0 v1 v2 = coe d_stackMem_470 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1292 ~v0 = du_writeHeapMem_1292
du_writeHeapMem_1292 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1292 = coe du_writeHeapMem_698
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1294 ~v0 = du_writeHeapMem'45'aux_1294
du_writeHeapMem'45'aux_1294 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1294 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_692 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLoc_1296 v0 = coe d_writeLoc_726 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1298 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1300 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1300 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1302 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1304 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1306 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1308 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1310 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1310 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLocToHeap_1312 ~v0 = du_writeLocToHeap_1312
du_writeLocToHeap_1312 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
du_writeLocToHeap_1312 = coe du_writeLocToHeap_718
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_456
d_writeLocToStack_1314 v0 = coe d_writeLocToStack_708 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1316 v0 = coe d_writeStackMem_674 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1318 ~v0 = du_writeStackMem'45'aux_1318
du_writeStackMem'45'aux_1318 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1318 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_666 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'load'45'with'45'value_1320 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1320 v1 v2
du_exec'45'load'45'with'45'value_1320 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
du_exec'45'load'45'with'45'value_1320 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_476 (coe du_writeReg_164 (d_regs_468 (coe v3)) v0 v2)
                  (coe d_stackMem_470 (coe v3)) (coe d_heapMem_472 (coe v3))
                  (coe d_halted_474 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_476 (coe d_regs_468 (coe v2))
                  (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
d_exec'45'load'45'via'45'resolved_1332 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1332 v1 v2
du_exec'45'load'45'via'45'resolved_1332 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
du_exec'45'load'45'via'45'resolved_1332 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1320 v0
                  (coe du_readLoc_646 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_476 (coe d_regs_468 (coe v2))
                  (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'store'45'via'45'resolved_1344 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_726 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_476 (coe d_regs_468 (coe v3))
                  (coe d_stackMem_470 (coe v3)) (coe d_heapMem_472 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1354 ~v0 v1 = du_slot'45'base_1354 v1
du_slot'45'base_1354 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1354 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1234 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_456 -> T_LocState_456
d_exec'45'lea'45'indexed'45'via_1358 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1358 v1
du_exec'45'lea'45'indexed'45'via_1358 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_456 -> T_LocState_456
du_exec'45'lea'45'indexed'45'via_1358 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_476
                  (coe
                     du_writeReg_164 (d_regs_468 (coe v3)) (coe C_Input1_56)
                     (coe C_SV'45'Ptr_70 (coe du_offsetLoc_92 (coe v1) (coe v2))))
                  (coe d_stackMem_470 (coe v3)) (coe d_heapMem_472 (coe v3))
                  (coe d_halted_474 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_476 (coe d_regs_468 (coe v2))
                  (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
d_exec'45'load'45'suc'45'via'45'resolved_1370 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1370 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1370 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
du_exec'45'load'45'suc'45'via'45'resolved_1370 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1320 v0
                  (coe du_readLoc_646 (coe v3) (coe du_sucLoc_82 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_476 (coe d_regs_468 (coe v2))
                  (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'store'45'suc'45'via'45'resolved_1382 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_726
                  (coe v0) (coe v4) (coe du_sucLoc_82 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_476 (coe d_regs_468 (coe v3))
                  (coe d_stackMem_470 (coe v3)) (coe d_heapMem_472 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1270 -> T_LocState_456 -> T_LocState_456
d_exec_1392 v0 v1
  = case coe v1 of
      C_load_1274 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1332 v2
                  (coe du_resolveSourceExt_1240 (coe d_regs_468 (coe v4)) (coe v3))
                  v4)
      C_store_1276 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1344 v0
                  (coe du_resolveSourceExt_1240 (coe d_regs_468 (coe v4)) (coe v2))
                  (coe du_readReg_152 (coe d_regs_468 (coe v4)) (coe v3)) v4)
      C_mov_1278 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_476
                  (coe
                     du_writeReg_164 (d_regs_468 (coe v4)) v2
                     (coe du_readReg_152 (coe d_regs_468 (coe v4)) (coe v3)))
                  (coe d_stackMem_470 (coe v4)) (coe d_heapMem_472 (coe v4))
                  (coe d_halted_474 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1418 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1424 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1270] -> T_LocState_456 -> T_LocState_456
d_execList_1426 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_474 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1426 (coe v0) (coe v4) (coe d_exec_1392 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1458 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1458 v0 v1 = coe d_heapMem_472 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1460 ~v0 = du_readLoc_1460
du_readLoc_1460 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1460 = coe du_readLoc_646
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1462 ::
  T_LocState_456 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1462 v0 v1 v2 = coe d_stackMem_470 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1464 ~v0 = du_writeHeapMem_1464
du_writeHeapMem_1464 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1464 = coe du_writeHeapMem_698
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1466 ~v0 = du_writeHeapMem'45'aux_1466
du_writeHeapMem'45'aux_1466 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1466 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_692 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLoc_1468 v0 = coe d_writeLoc_726 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1470 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1472 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1472 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1474 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1476 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1478 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1480 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1482 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1482 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1484 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLocToHeap_1484 ~v0 = du_writeLocToHeap_1484
du_writeLocToHeap_1484 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
du_writeLocToHeap_1484 = coe du_writeLocToHeap_718
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_456
d_writeLocToStack_1486 v0 = coe d_writeLocToStack_708 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1488 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1488 v0 = coe d_writeStackMem_674 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1490 ~v0 = du_writeStackMem'45'aux_1490
du_writeStackMem'45'aux_1490 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1490 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_666 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1270 -> T_LocState_456 -> T_LocState_456
d_exec_1494 v0 = coe d_exec_1392 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_456 -> T_LocState_456
d_exec'45'lea'45'indexed'45'via_1496 ~v0
  = du_exec'45'lea'45'indexed'45'via_1496
du_exec'45'lea'45'indexed'45'via_1496 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_456 -> T_LocState_456
du_exec'45'lea'45'indexed'45'via_1496
  = coe du_exec'45'lea'45'indexed'45'via_1358
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1498 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1500 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
d_exec'45'load'45'suc'45'via'45'resolved_1502 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1502
du_exec'45'load'45'suc'45'via'45'resolved_1502 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
du_exec'45'load'45'suc'45'via'45'resolved_1502
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1370
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
d_exec'45'load'45'via'45'resolved_1504 ~v0
  = du_exec'45'load'45'via'45'resolved_1504
du_exec'45'load'45'via'45'resolved_1504 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
du_exec'45'load'45'via'45'resolved_1504
  = coe du_exec'45'load'45'via'45'resolved_1332
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'load'45'with'45'value_1506 ~v0
  = du_exec'45'load'45'with'45'value_1506
du_exec'45'load'45'with'45'value_1506 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
du_exec'45'load'45'with'45'value_1506
  = coe du_exec'45'load'45'with'45'value_1320
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'store'45'suc'45'via'45'resolved_1508 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1382 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'store'45'via'45'resolved_1510 v0
  = coe d_exec'45'store'45'via'45'resolved_1344 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1270] -> T_LocState_456 -> T_LocState_456
d_execList_1512 v0 = coe d_execList_1426 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1514 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1514 ~v0 = du_slot'45'base_1514
du_slot'45'base_1514 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1514 = coe du_slot'45'base_1354
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 -> T_LocSourceExt_1222 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_1516 ~v0 v1 v2
  = du_resolved'45'readLoc_1516 v1 v2
du_resolved'45'readLoc_1516 ::
  T_LocState_456 -> T_LocSourceExt_1222 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_1516 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1240 (coe d_regs_468 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_646 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1546 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1616 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1692 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1722 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1778 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1830 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_1882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_1882 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_1898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_1898 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_1916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_1916 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_1930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_1930 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_1948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_1948 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2014 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2014 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2038 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2066 = ()
data T_FlatCtrl_2066
  = C_c'45'label_2068 Integer | C_c'45'jmp_2070 Integer |
    C_c'45'branch'45'scratch'45'zero_2072 Integer |
    C_c'45'branch'45'tag'45'zero_2074 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2076 = ()
data T_AbstractInstr_2076
  = C_mov'45'to'45'output_2078 | C_mov'45'to'45'input_2080 |
    C_mov'45'output'45'to'45'input2_2082 |
    C_mov'45'input2'45'to'45'output_2084 | C_load'45'indirect_2086 |
    C_load'45'indirect'45'suc_2088 |
    C_load'45'from'45'slot_2090 Integer |
    C_store'45'at'45'slot_2092 Integer | C_store'45'indirect_2094 |
    C_store'45'indirect'45'suc_2096 | C_lea'45'slot_2098 Integer |
    C_restore'45'input_2100 Integer |
    C_instr'45'alloc'45'stack_2102 Integer |
    C_instr'45'dealloc'45'stack_2104 Integer |
    C_instr'45'reclaim'45'to_2106 Integer |
    C_instr'45'push'45'frame_2108 Integer |
    C_instr'45'pop'45'frame_2110 | C_instr'45'call'45'closure_2112 |
    C_worklist'45'init_2114 Integer | C_worklist'45'push_2116 Integer |
    C_worklist'45'pop_2118 Integer | C_worklist'45'check_2120 Integer |
    C_instr'45'sigop_2126 MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.Type.T_Type_112
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 |
    C_instr'45'load'45'const_2130 MAlonzo.Code.Once.Type.T_Type_112
                                  MAlonzo.Code.Once.Type.T_FitsInReg_196 AgdaAny |
    C_instr'45'load'45'code'45'addr_2132 Integer |
    C_instr'45'save'45'closure'45'reg_2134 |
    C_instr'45'load'45'tag'45'lit_2136 Integer |
    C_instr'45'case'45'on'45'tag_2138 [T_AbstractInstr_2076]
                                      [T_AbstractInstr_2076] |
    C_instr'45'alloc'45'heap_2140 Integer |
    C_instr'45'loop_2142 [T_AbstractInstr_2076] |
    C_instr'45'reg'45'op_2144 T_RegOp_422 |
    C_instr'45'ctrl_2146 T_FlatCtrl_2066 |
    C_lea'45'indexed_2148 Integer
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2150 :: ()
d_AbstractTrace_2150 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2152 = ()
data T_TreeTrace_2152
  = C_ε_2154 | C_instr_2156 T_AbstractInstr_2076 |
    C__'9656'__2158 T_TreeTrace_2152 T_TreeTrace_2152 |
    C_branch_2160 Integer T_TreeTrace_2152 T_TreeTrace_2152 |
    C_call'45'sub_2162 T_TreeTrace_2152 |
    C_flat_2164 [T_AbstractInstr_2076]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2166 :: [T_AbstractInstr_2076] -> T_TreeTrace_2152
d_flatToTree_2166 v0
  = case coe v0 of
      [] -> coe C_ε_2154
      (:) v1 v2
        -> coe
             C__'9656'__2158 (coe C_instr_2156 (coe v1))
             (coe d_flatToTree_2166 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2172 :: T_TreeTrace_2152 -> [T_AbstractInstr_2076]
d_treeToFlat_2172 v0
  = case coe v0 of
      C_ε_2154 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2156 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2158 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2172 (coe v1)) (coe d_treeToFlat_2172 (coe v2))
      C_branch_2160 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2172 (coe v2)) (coe d_treeToFlat_2172 (coe v3))
      C_call'45'sub_2162 v1 -> coe d_treeToFlat_2172 (coe v1)
      C_flat_2164 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2188 ::
  Integer -> T_TreeTrace_2152 -> [T_AbstractInstr_2076]
d_treeToRunnable_2188 v0 v1
  = case coe v1 of
      C_ε_2154 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2156 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2158 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2188 (coe v0) (coe v2))
             (coe d_treeToRunnable_2188 (coe v0) (coe v3))
      C_branch_2160 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2188 (coe v0) (coe v3))
             (coe d_treeToRunnable_2188 (coe v0) (coe v4))
      C_call'45'sub_2162 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2116 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2188 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2118 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2164 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2218 ::
  Integer -> T_TreeTrace_2152 -> [T_AbstractInstr_2076]
d_treeToRunnableWithInit_2218 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2114 (coe v0))
      (coe d_treeToRunnable_2188 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2262 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_readHeapLoc_2262 v0 v1 = coe d_heapMem_472 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_2264 ~v0 = du_readLoc_2264
du_readLoc_2264 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_2264 = coe du_readLoc_646
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2266 ::
  T_LocState_456 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_2266 v0 v1 v2 = coe d_stackMem_470 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
d_writeHeapMem_2268 ~v0 = du_writeHeapMem_2268
du_writeHeapMem_2268 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe T_StoredValue_66
du_writeHeapMem_2268 = coe du_writeHeapMem_698
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_2270 ~v0 = du_writeHeapMem'45'aux_2270
du_writeHeapMem'45'aux_2270 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_2270 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_692 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLoc_2272 v0 = coe d_writeLoc_726 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2274 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2276 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2276 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2278 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2280 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2282 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2284 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2286 ::
  T_LocState_456 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_124 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2286 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
d_writeLocToHeap_2288 ~v0 = du_writeLocToHeap_2288
du_writeLocToHeap_2288 ::
  T_LocState_456 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_StoredValue_66 -> T_LocState_456
du_writeLocToHeap_2288 = coe du_writeLocToHeap_718
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_456
d_writeLocToStack_2290 v0 = coe d_writeLocToStack_708 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_2292 v0 = coe d_writeStackMem_674 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_2294 ~v0 = du_writeStackMem'45'aux_2294
du_writeStackMem'45'aux_2294 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_2294 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_666 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1270 -> T_LocState_456 -> T_LocState_456
d_exec_2298 v0 = coe d_exec_1392 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_456 -> T_LocState_456
d_exec'45'lea'45'indexed'45'via_2300 ~v0
  = du_exec'45'lea'45'indexed'45'via_2300
du_exec'45'lea'45'indexed'45'via_2300 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_456 -> T_LocState_456
du_exec'45'lea'45'indexed'45'via_2300
  = coe du_exec'45'lea'45'indexed'45'via_1358
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2302 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2304 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
d_exec'45'load'45'suc'45'via'45'resolved_2306 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2306
du_exec'45'load'45'suc'45'via'45'resolved_2306 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
du_exec'45'load'45'suc'45'via'45'resolved_2306
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1370
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
d_exec'45'load'45'via'45'resolved_2308 ~v0
  = du_exec'45'load'45'via'45'resolved_2308
du_exec'45'load'45'via'45'resolved_2308 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> T_LocState_456
du_exec'45'load'45'via'45'resolved_2308
  = coe du_exec'45'load'45'via'45'resolved_1332
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'load'45'with'45'value_2310 ~v0
  = du_exec'45'load'45'with'45'value_2310
du_exec'45'load'45'with'45'value_2310 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
du_exec'45'load'45'with'45'value_2310
  = coe du_exec'45'load'45'with'45'value_1320
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'store'45'suc'45'via'45'resolved_2312 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1382 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_456 -> T_LocState_456
d_exec'45'store'45'via'45'resolved_2314 v0
  = coe d_exec'45'store'45'via'45'resolved_1344 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1270] -> T_LocState_456 -> T_LocState_456
d_execList_2316 v0 = coe d_execList_1426 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2318 ~v0 = du_slot'45'base_2318
du_slot'45'base_2318 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2318 = coe du_slot'45'base_1354
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_2322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_2322 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_2324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  T_LocState_456 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_2324 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-no-halt
d_load'45'no'45'halt_2326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2326 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-halted
d_load'45'preserves'45'halted_2328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2328 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-heapMem
d_load'45'preserves'45'heapMem_2330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_2330 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-reg
d_load'45'preserves'45'reg_2332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_2332 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-preserves-stackMem
d_load'45'preserves'45'stackMem_2334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_2334 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.load-result
d_load'45'result_2336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1222 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_2336 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2338 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-reg
d_mov'45'preserves'45'reg_2340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2340 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2342 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.mov-result
d_mov'45'result_2344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_456 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2344 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 ->
  T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2346 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.resolved-readLoc
d_resolved'45'readLoc_2348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 -> T_LocSourceExt_1222 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_2348 ~v0 = du_resolved'45'readLoc_2348
du_resolved'45'readLoc_2348 ::
  T_LocState_456 -> T_LocSourceExt_1222 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_2348 = coe du_resolved'45'readLoc_1516
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2350 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2350 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2350 ::
  Maybe T_StoredValue_66 ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2350 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe du_writeReg_164 (d_regs_468 (coe v1)) (coe C_Output_60) v3)
                (coe d_stackMem_470 (coe v1)) (coe d_heapMem_472 (coe v1))
                (coe d_halted_474 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476 (coe d_regs_468 (coe v1))
                (coe d_stackMem_470 (coe v1)) (coe d_heapMem_472 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2362 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2362 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2362 ::
  Maybe T_StoredValue_66 ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2362 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe du_writeReg_164 (d_regs_468 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_470 (coe v1)) (coe d_heapMem_472 (coe v1))
                (coe d_halted_474 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476 (coe d_regs_468 (coe v1))
                (coe d_stackMem_470 (coe v1)) (coe d_heapMem_472 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2380 ::
  T_StoredValue_66 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2380 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2386 ::
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2386 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2394 ::
  T_StoredValue_66 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2394 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2400 ::
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2400 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66
d_unit'45'storedvalue_2402 ~v0 = du_unit'45'storedvalue_2402
du_unit'45'storedvalue_2402 :: T_StoredValue_66
du_unit'45'storedvalue_2402
  = coe
      C_SV'45'Lit_76 (coe MAlonzo.Code.Once.Type.C_Int_136)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2408 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2408 v3 v4
du_combine'45'typed_2408 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2408 v0 v1
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
d_readTyped'45'int_2414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 -> Maybe Integer
d_readTyped'45'int_2414 ~v0 v1 = du_readTyped'45'int_2414 v1
du_readTyped'45'int_2414 :: Maybe T_StoredValue_66 -> Maybe Integer
du_readTyped'45'int_2414 v0
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
d_readTyped'45'pair_2422 ::
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
d_readTyped'45'pair_2422 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'pair_2422 v3 v4 v5 v6
du_readTyped'45'pair_2422 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2422 v0 v1 v2 v3
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
                                -> coe du_combine'45'typed_2408 (coe v0 v6) (coe v1 v8)
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_66 -> Maybe AgdaAny
d_readReg'45'typed_2438 ~v0 v1 v2 = du_readReg'45'typed_2438 v1 v2
du_readReg'45'typed_2438 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_StoredValue_66 -> Maybe AgdaAny
du_readReg'45'typed_2438 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
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
d_readTyped_2444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> Maybe AgdaAny
d_readTyped_2444 ~v0 v1 v2 v3 = du_readTyped_2444 v1 v2 v3
du_readTyped_2444 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_456 -> Maybe AgdaAny
du_readTyped_2444 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
           -> coe
                du_readTyped'45'pair_2422
                (coe (\ v6 -> coe du_readTyped_2444 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2444 (coe v5) (coe v6) (coe v2)))
                (coe du_readLoc_646 (coe v2) (coe v1))
                (coe du_readLoc_646 (coe v2) (coe du_sucLoc_82 (coe v1)))
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe
                du_readTyped'45'int_2414 (coe du_readLoc_646 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2474
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_456 -> T_StoredValue_66
d_pure'45'sigop'45'output_2480 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_2502 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_204 (coe v2))
      (coe
         du_sv'45'as'45'loc_1234
         (coe du_readReg_152 (coe d_regs_468 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_66
d_pure'45'sigop'45'out'45'val_2486 ~v0 ~v1 v2 v3 v4 v5
  = du_pure'45'sigop'45'out'45'val_2486 v2 v3 v4 v5
du_pure'45'sigop'45'out'45'val_2486 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe AgdaAny -> T_StoredValue_66
du_pure'45'sigop'45'out'45'val_2486 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             C_SV'45'Lit_76 (coe v0) (coe v2)
             (coe MAlonzo.Code.Once.SigOp.Info.du_semM_188 v1 v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2402
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_2502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_456 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_2502 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    du_pure'45'sigop'45'out'45'val_2486 (coe v2) (coe v3) (coe v7)
                    (coe du_readTyped_2444 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_pure'45'sigop'45'out'45'val_2486 (coe v2) (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2438 (coe v1)
                       (coe du_readReg_152 (coe d_regs_468 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2474 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_2538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_456 -> T_StoredValue_66
d_exec'45'sigop'45'output'45'of_2538 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_124
        -> coe
             d_pure'45'sigop'45'output_2480 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_126
        -> coe du_unit'45'storedvalue_2402
      MAlonzo.Code.Once.SigOp.Info.C_Halts_128
        -> coe du_unit'45'storedvalue_2402
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_2548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_456 -> T_StoredValue_66
d_exec'45'sigop'45'output_2548 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_2538 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_456 -> Bool
d_exec'45'sigop'45'halts'45'of_2558 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_2558 v3
du_exec'45'sigop'45'halts'45'of_2558 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_120 -> Bool
du_exec'45'sigop'45'halts'45'of_2558 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_Halts_128
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  T_LocState_456 -> Bool
d_exec'45'sigop'45'halts_2564 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_2564 v3
du_exec'45'sigop'45'halts_2564 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 -> Bool
du_exec'45'sigop'45'halts_2564 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_2558
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_212 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_2570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 -> Maybe T_StoredValue_66
d_case'45'tag'45'at_2570 ~v0 v1 = du_case'45'tag'45'at_2570 v1
du_case'45'tag'45'at_2570 ::
  T_LocState_456 -> Maybe T_StoredValue_66
du_case'45'tag'45'at_2570 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1234
              (coe d_input1_138 (coe d_regs_468 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_646 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_2584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2076 ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_2584 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2078
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2080
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Output_60)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_mov'45'output'45'to'45'input2_2082
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Input2_58)
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Output_60)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_mov'45'input2'45'to'45'output_2084
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Input2_58)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_load'45'indirect_2086
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1332 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1234
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2088
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1370 (coe C_Output_60)
                (coe
                   du_sv'45'as'45'loc_1234
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2090 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2350
             (coe
                du_readLoc_646 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_586 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2092 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_726 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_586 (coe v3)) (coe v4))
                (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_store'45'indirect_2094
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1344 v0
                (coe
                   du_sv'45'as'45'loc_1234
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2096
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1382 v0
                (coe
                   du_sv'45'as'45'loc_1234
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Output_60))
                v2)
             (coe v3)
      C_lea'45'slot_2098 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_586 (coe v3)) (coe v4))))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_restore'45'input_2100 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2362
             (coe
                du_readLoc_646 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_586 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2102 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe du_incrStackSlot_192 (coe d_regs_468 (coe v2)) (coe v4))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe
                C_mkAllocState_594 (coe d_current'45'frame_586 (coe v3))
                (coe d_saved'45'frames_588 (coe v3))
                (coe addInt (coe d_next'45'slot_590 (coe v3)) (coe v4))
                (coe d_next'45'heap'45'ref_592 (coe v3)))
      C_instr'45'dealloc'45'stack_2104 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe du_decrStackSlot_200 (coe d_regs_468 (coe v2)) (coe v4))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_instr'45'reclaim'45'to_2106 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                C_mkAllocState_594 (coe d_current'45'frame_586 (coe v3))
                (coe d_saved'45'frames_588 (coe v3)) (coe v4)
                (coe d_next'45'heap'45'ref_592 (coe v3)))
      C_instr'45'push'45'frame_2108 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeStackSlot_184 (coe d_regs_468 (coe v2))
                   (coe (0 :: Integer)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_instr'45'pop'45'frame_2110
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2112
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2114 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2116 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_726 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_586 (coe v3)) (coe v4))
                (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Output_60)))
             (coe v3)
      C_worklist'45'pop_2118 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2350
             (coe
                du_readLoc_646 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_586 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2120 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2126 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (d_exec'45'sigop'45'output_2548
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe du_exec'45'sigop'45'halts_2564 (coe v6)))
             (coe v3)
      C_instr'45'load'45'const_2130 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Lit_76 (coe v4) (coe v5) (coe v6)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2132 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Code_78 (coe v4)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2136 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe C_SV'45'Tag_72 (coe v4)))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2138 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_2590 (coe v0)
             (coe du_case'45'tag'45'at_2570 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2140 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476
                (coe
                   du_writeReg_164 (d_regs_468 (coe v2)) (coe C_Output_60)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_592 (coe v3)))))))
                (coe d_stackMem_470 (coe v2)) (coe d_heapMem_472 (coe v2))
                (coe d_halted_474 (coe v2)))
             (coe
                C_mkAllocState_594 (coe d_current'45'frame_586 (coe v3))
                (coe d_saved'45'frames_588 (coe v3))
                (coe d_next'45'slot_590 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_592 (coe v3))))))
      C_instr'45'loop_2142 v4
        -> coe
             d_exec'45'loop_2588 (coe v0) (coe (1000000 :: Integer)) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2144 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_496 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2146 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2148 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1358
                (coe
                   du_slot'45'base_1354
                   (coe
                      du_readLoc_646 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_586 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_450
                   (coe du_readReg_152 (coe d_regs_468 (coe v2)) (coe C_Scratch_62)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_2586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2076] ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_2586 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_474 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_2586 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_2584 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_2584 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2076] ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_2588 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476 (coe d_regs_468 (coe v3))
                (coe d_stackMem_470 (coe v3)) (coe d_heapMem_472 (coe v3))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v4)
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v6 = d_halted_474 (coe v3) in
              coe
                (if coe v6
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4)
                   else (let v7 = d_scratch_146 (coe d_regs_468 (coe v3)) in
                         coe
                           (let v8
                                  = d_exec'45'loop_2588
                                      (coe v0) (coe v5) (coe v2)
                                      (coe
                                         C_mkLocState_476
                                         (coe
                                            d_regs_468
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2586 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe d_stackMem_470 (coe v3))
                                         (coe
                                            d_heapMem_472
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2586 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe
                                            d_halted_474
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_exec'45'trace_2586 (coe v0) (coe v2) (coe v3)
                                                  (coe v4)))))
                                      (coe
                                         C_mkAllocState_594 (coe d_current'45'frame_586 (coe v4))
                                         (coe
                                            d_saved'45'frames_588
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_exec'45'trace_2586 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))
                                         (coe d_next'45'slot_590 (coe v4))
                                         (coe
                                            d_next'45'heap'45'ref_592
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_exec'45'trace_2586 (coe v0) (coe v2) (coe v3)
                                                  (coe v4))))) in
                            coe
                              (case coe v7 of
                                 C_SV'45'Tag_72 v9
                                   -> case coe v9 of
                                        0 -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                               (coe v4)
                                        _ -> coe v8
                                 _ -> coe v8)))))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_2590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  [T_AbstractInstr_2076] ->
  [T_AbstractInstr_2076] ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_2590 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_70 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_476 (coe d_regs_468 (coe v4))
                       (coe d_stackMem_470 (coe v4)) (coe d_heapMem_472 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Tag_72 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_2586 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_2586 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_76 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_476 (coe d_regs_468 (coe v4))
                       (coe d_stackMem_470 (coe v4)) (coe d_heapMem_472 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             C_SV'45'Code_78 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_476 (coe d_regs_468 (coe v4))
                       (coe d_stackMem_470 (coe v4)) (coe d_heapMem_472 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_476 (coe d_regs_468 (coe v4))
                (coe d_stackMem_470 (coe v4)) (coe d_heapMem_472 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_2932 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2076 ->
  [T_AbstractInstr_2076] ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_2932 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_2978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2076 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_2978 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2076 -> ()) -> [T_AbstractInstr_2076] -> ()
d_AllI_3012 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_510 -> AgdaAny) ->
  (T_AbstractInstr_2076 -> ()) ->
  (T_AbstractInstr_2076 ->
   T_LocState_456 ->
   T_AllocState_510 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2076] ->
  AgdaAny ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3040 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_510 -> AgdaAny) ->
  (T_AbstractInstr_2076 -> ()) ->
  (T_AbstractInstr_2076 ->
   T_LocState_456 ->
   T_AllocState_510 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2076] ->
  [T_AbstractInstr_2076] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3130 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_456 -> T_AllocState_510 -> Integer -> Maybe Integer
d_getTag_3262 ~v0 v1 v2 v3 = du_getTag_3262 v1 v2 v3
du_getTag_3262 ::
  T_LocState_456 -> T_AllocState_510 -> Integer -> Maybe Integer
du_getTag_3262 v0 v1 v2
  = let v3
          = coe d_stackMem_470 v0 (d_current'45'frame_586 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2152 ->
  T_LocState_456 ->
  T_AllocState_510 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3286 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2154
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2156 v4
        -> let v5 = d_halted_474 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_2584 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2158 v4 v5
        -> let v6 = d_halted_474 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3286 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3286 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3286 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2160 v4 v5 v6
        -> let v7 = d_halted_474 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_470 v2 (d_current'45'frame_586 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3286 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3286 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3286 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3286 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3286 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2162 v4
        -> let v5 = d_halted_474 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3286 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2164 v4
        -> coe d_exec'45'trace_2586 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_3446 ::
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_3446 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_3464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2152 ->
  T_TreeTrace_2152 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_3464 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_3510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2076 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_3510 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_3550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2152 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_3550 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_3590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2076] ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_3590 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-++
d_exec'45'trace'45''43''43'_3610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2076] ->
  [T_AbstractInstr_2076] ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45''43''43'_3610 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'
d_exec'45'abstract'45'preserves'45'not'45'halted''_3668
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec._.exec-abstract-preserves-not-halted'"
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_3676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2152 ->
  T_LocState_456 ->
  T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_3676 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_3676
du_exec'45'tree'45'flat'45'equiv'45'simple_3676 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_3676
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
