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
import qualified MAlonzo.Code.Data.Bool.Base
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
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
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
    C_SV'45'Lit_76 MAlonzo.Code.Once.Spec.Type.T_Type_8
                   MAlonzo.Code.Once.Type.T_FitsInReg_56 AgdaAny |
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
             (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v1))
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
                MAlonzo.Code.Once.Memory.HeapAddress.d_offsetHL_90 (coe v2)
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
d__'8799'R__116 ::
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'R__116 v0 v1
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
d_Registers_120 a0 = ()
data T_Registers_120
  = C_mkRegs_140 T_StoredValue_66 T_StoredValue_66 T_StoredValue_66
                 T_StoredValue_66
-- Once.CCC.Machine.SMCore.Registers.input1
d_input1_132 :: T_Registers_120 -> T_StoredValue_66
d_input1_132 v0
  = case coe v0 of
      C_mkRegs_140 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.output
d_output_134 :: T_Registers_120 -> T_StoredValue_66
d_output_134 v0
  = case coe v0 of
      C_mkRegs_140 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.scratch
d_scratch_136 :: T_Registers_120 -> T_StoredValue_66
d_scratch_136 v0
  = case coe v0 of
      C_mkRegs_140 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.Registers.count
d_count_138 :: T_Registers_120 -> T_StoredValue_66
d_count_138 v0
  = case coe v0 of
      C_mkRegs_140 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.readReg
d_readReg_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_120 -> T_AbstractReg_54 -> T_StoredValue_66
d_readReg_144 ~v0 v1 v2 = du_readReg_144 v1 v2
du_readReg_144 ::
  T_Registers_120 -> T_AbstractReg_54 -> T_StoredValue_66
du_readReg_144 v0 v1
  = case coe v1 of
      C_Input1_56 -> coe d_input1_132 (coe v0)
      C_Output_58 -> coe d_output_134 (coe v0)
      C_Scratch_60 -> coe d_scratch_136 (coe v0)
      C_Count_62 -> coe d_count_138 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg
d_writeReg_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_120 ->
  T_AbstractReg_54 -> T_StoredValue_66 -> T_Registers_120
d_writeReg_156 ~v0 v1 v2 = du_writeReg_156 v1 v2
du_writeReg_156 ::
  T_Registers_120 ->
  T_AbstractReg_54 -> T_StoredValue_66 -> T_Registers_120
du_writeReg_156 v0 v1
  = case coe v1 of
      C_Input1_56
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_140 (coe v2) (coe d_output_134 (coe v0))
                  (coe d_scratch_136 (coe v0)) (coe d_count_138 (coe v0)))
      C_Output_58
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_140 (coe d_input1_132 (coe v0)) (coe v2)
                  (coe d_scratch_136 (coe v0)) (coe d_count_138 (coe v0)))
      C_Scratch_60
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_140 (coe d_input1_132 (coe v0))
                  (coe d_output_134 (coe v0)) (coe v2) (coe d_count_138 (coe v0)))
      C_Count_62
        -> coe
             (\ v2 ->
                coe
                  C_mkRegs_140 (coe d_input1_132 (coe v0))
                  (coe d_output_134 (coe v0)) (coe d_scratch_136 (coe v0)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.writeReg-preserves
d_writeReg'45'preserves_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_120 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'preserves_188 = erased
-- Once.CCC.Machine.SMCore.writeReg-same
d_writeReg'45'same_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_120 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'same_310 = erased
-- Once.CCC.Machine.SMCore.writeReg-overwrite
d_writeReg'45'overwrite_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_120 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeReg'45'overwrite_338 = erased
-- Once.CCC.Machine.SMCore.RegOp
d_RegOp_364 = ()
data T_RegOp_364
  = C_scratch'45'one_366 | C_scratch'45'zero_368 |
    C_scratch'45'dec_370 | C_scratch'45'load'45'count_372 |
    C_count'45'zero_374 | C_count'45'inc_376 | C_out'45'nz_378
-- Once.CCC.Machine.SMCore.sv-nz
d_sv'45'nz_382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'nz_382 ~v0 v1 = du_sv'45'nz_382 v1
du_sv'45'nz_382 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'nz_382 v0
  = case coe v0 of
      C_SV'45'Ptr_70 v1 -> coe C_SV'45'Tag_72 (coe (1 :: Integer))
      C_SV'45'Tag_72 v1
        -> coe
             C_SV'45'Tag_72
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe eqInt (coe v1) (coe (0 :: Integer))) (coe (0 :: Integer))
                (coe (1 :: Integer)))
      C_SV'45'Lit_76 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_58
               -> coe
                    C_SV'45'Tag_72
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe eqInt (coe v3) (coe (0 :: Integer))) (coe (0 :: Integer))
                       (coe (1 :: Integer)))
             MAlonzo.Code.Once.Type.C_fits'45'float_60
               -> coe C_SV'45'Tag_72 (coe (1 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_SV'45'Code_78 v1 -> coe C_SV'45'Tag_72 (coe (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sv-succ
d_sv'45'succ_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'succ_390 ~v0 v1 = du_sv'45'succ_390 v1
du_sv'45'succ_390 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'succ_390 v0
  = case coe v0 of
      C_SV'45'Ptr_70 v1 -> coe C_SV'45'Tag_72 (coe (1 :: Integer))
      C_SV'45'Tag_72 v1
        -> coe C_SV'45'Tag_72 (coe addInt (coe (1 :: Integer)) (coe v1))
      C_SV'45'Lit_76 v1 v2 v3 -> coe C_SV'45'Tag_72 (coe (1 :: Integer))
      C_SV'45'Code_78 v1 -> coe C_SV'45'Tag_72 (coe (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sv-pred
d_sv'45'pred_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 -> T_StoredValue_66
d_sv'45'pred_396 ~v0 v1 = du_sv'45'pred_396 v1
du_sv'45'pred_396 :: T_StoredValue_66 -> T_StoredValue_66
du_sv'45'pred_396 v0
  = case coe v0 of
      C_SV'45'Ptr_70 v1 -> coe C_SV'45'Tag_72 (coe (0 :: Integer))
      C_SV'45'Tag_72 v1
        -> case coe v1 of
             0 -> coe C_SV'45'Tag_72 (coe (0 :: Integer))
             _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe C_SV'45'Tag_72 (coe v2))
      C_SV'45'Lit_76 v1 v2 v3 -> coe C_SV'45'Tag_72 (coe (0 :: Integer))
      C_SV'45'Code_78 v1 -> coe C_SV'45'Tag_72 (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.sv-tag-val
d_sv'45'tag'45'val_402 :: T_StoredValue_66 -> Integer
d_sv'45'tag'45'val_402 v0
  = case coe v0 of
      C_SV'45'Ptr_70 v1 -> coe (0 :: Integer)
      C_SV'45'Tag_72 v1 -> coe v1
      C_SV'45'Lit_76 v1 v2 v3 -> coe (0 :: Integer)
      C_SV'45'Code_78 v1 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState
d_LocState_408 a0 = ()
data T_LocState_408
  = C_mkLocState_432 T_Registers_120
                     (AgdaAny -> Integer -> Maybe T_StoredValue_66)
                     (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
                      Maybe T_StoredValue_66)
                     Bool [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
-- Once.CCC.Machine.SMCore.LocState.regs
d_regs_422 :: T_LocState_408 -> T_Registers_120
d_regs_422 v0
  = case coe v0 of
      C_mkLocState_432 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.stackMem
d_stackMem_424 ::
  T_LocState_408 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_stackMem_424 v0
  = case coe v0 of
      C_mkLocState_432 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.heapMem
d_heapMem_426 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_heapMem_426 v0
  = case coe v0 of
      C_mkLocState_432 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.halted
d_halted_428 :: T_LocState_408 -> Bool
d_halted_428 v0
  = case coe v0 of
      C_mkLocState_432 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.LocState.ev-log
d_ev'45'log_430 ::
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_ev'45'log_430 v0
  = case coe v0 of
      C_mkLocState_432 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.setReg
d_setReg_436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_364 -> T_Registers_120 -> T_Registers_120
d_setReg_436 ~v0 v1 v2 = du_setReg_436 v1 v2
du_setReg_436 :: T_RegOp_364 -> T_Registers_120 -> T_Registers_120
du_setReg_436 v0 v1
  = case coe v0 of
      C_scratch'45'one_366
        -> coe
             du_writeReg_156 v1 (coe C_Scratch_60)
             (coe C_SV'45'Tag_72 (coe (1 :: Integer)))
      C_scratch'45'zero_368
        -> coe
             du_writeReg_156 v1 (coe C_Scratch_60)
             (coe C_SV'45'Tag_72 (coe (0 :: Integer)))
      C_scratch'45'dec_370
        -> coe
             du_writeReg_156 v1 (coe C_Scratch_60)
             (coe
                du_sv'45'pred_396 (coe du_readReg_144 (coe v1) (coe C_Scratch_60)))
      C_scratch'45'load'45'count_372
        -> coe
             du_writeReg_156 v1 (coe C_Scratch_60)
             (coe du_readReg_144 (coe v1) (coe C_Count_62))
      C_count'45'zero_374
        -> coe
             du_writeReg_156 v1 (coe C_Count_62)
             (coe C_SV'45'Tag_72 (coe (0 :: Integer)))
      C_count'45'inc_376
        -> coe
             du_writeReg_156 v1 (coe C_Count_62)
             (coe
                du_sv'45'succ_390 (coe du_readReg_144 (coe v1) (coe C_Count_62)))
      C_out'45'nz_378
        -> coe
             du_writeReg_156 v1 (coe C_Output_58)
             (coe
                du_sv'45'nz_382 (coe du_readReg_144 (coe v1) (coe C_Output_58)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.exec-reg-op
d_exec'45'reg'45'op_454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_RegOp_364 -> T_LocState_408 -> T_LocState_408
d_exec'45'reg'45'op_454 ~v0 v1 v2 = du_exec'45'reg'45'op_454 v1 v2
du_exec'45'reg'45'op_454 ::
  T_RegOp_364 -> T_LocState_408 -> T_LocState_408
du_exec'45'reg'45'op_454 v0 v1
  = coe
      C_mkLocState_432
      (coe du_setReg_436 (coe v0) (coe d_regs_422 (coe v1)))
      (coe d_stackMem_424 (coe v1)) (coe d_heapMem_426 (coe v1))
      (coe d_halted_428 (coe v1)) (coe d_ev'45'log_430 (coe v1))
-- Once.CCC.Machine.SMCore.AllocMode
d_AllocMode_460 = ()
data T_AllocMode_460 = C_Stack_462 | C_Heap_464
-- Once.CCC.Machine.SMCore.size-with-aux
d_size'45'with'45'aux_472 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_size'45'with'45'aux_472 v0 v1 ~v2 v3 v4
  = du_size'45'with'45'aux_472 v0 v1 v3 v4
du_size'45'with'45'aux_472 ::
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_size'45'with'45'aux_472 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe v0)
             else coe seq (coe v5) (coe v2 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.size-with
d_size'45'with_488 ::
  Integer -> Integer -> (Integer -> Integer) -> Integer -> Integer
d_size'45'with_488 v0 v1 v2 v3
  = coe
      du_size'45'with'45'aux_472 (coe v0) (coe v3) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v1))
-- Once.CCC.Machine.SMCore.AllocState
d_AllocState_500 a0 = ()
data T_AllocState_500
  = C_mkAllocState_604 AgdaAny
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] Integer Integer Integer
                       (Integer -> Integer)
-- Once.CCC.Machine.SMCore.AllocState.current-frame
d_current'45'frame_592 :: T_AllocState_500 -> AgdaAny
d_current'45'frame_592 v0
  = case coe v0 of
      C_mkAllocState_604 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.saved-frames
d_saved'45'frames_594 ::
  T_AllocState_500 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_saved'45'frames_594 v0
  = case coe v0 of
      C_mkAllocState_604 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.frame-slots
d_frame'45'slots_596 :: T_AllocState_500 -> Integer
d_frame'45'slots_596 v0
  = case coe v0 of
      C_mkAllocState_604 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-slot
d_next'45'slot_598 :: T_AllocState_500 -> Integer
d_next'45'slot_598 v0
  = case coe v0 of
      C_mkAllocState_604 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.next-heap-ref
d_next'45'heap'45'ref_600 :: T_AllocState_500 -> Integer
d_next'45'heap'45'ref_600 v0
  = case coe v0 of
      C_mkAllocState_604 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AllocState.block-size
d_block'45'size_602 :: T_AllocState_500 -> Integer -> Integer
d_block'45'size_602 v0
  = case coe v0 of
      C_mkAllocState_604 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.readStackLoc
d_readStackLoc_648 ::
  T_LocState_408 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_648 v0 v1 v2 = coe d_stackMem_424 v0 v1 v2
-- Once.CCC.Machine.SMCore.MemOps.readHeapLoc
d_readHeapLoc_656 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_readHeapLoc_656 v0 v1 = coe d_heapMem_426 v0 v1
-- Once.CCC.Machine.SMCore.MemOps.readLoc
d_readLoc_662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_662 ~v0 v1 v2 = du_readLoc_662 v1 v2
du_readLoc_662 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_662 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v2 v3
        -> coe d_stackMem_424 v0 v2 v3
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v2
        -> coe d_heapMem_426 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeStackMem-aux
d_writeStackMem'45'aux_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_682 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_writeStackMem'45'aux_682 v5 v6 v7 v8
du_writeStackMem'45'aux_682 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_682 v0 v1 v2 v3
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
d_writeStackMem_690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_690 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_writeStackMem'45'aux_682
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__82 v0 v2 v5)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v6))
      (coe v1 v5 v6) (coe v4)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-aux
d_clear'45'frame'45'aux_712 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_712 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_clear'45'frame'45'aux_712 v5 v6 v7
du_clear'45'frame'45'aux_712 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_712 v0 v1 v2
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
d_clear'45'frame_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_718 v0 v1 v2 v3 v4 v5
  = coe
      du_clear'45'frame'45'aux_712
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d__'8799'F__82 v0 v2 v4)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v5)
         (coe v3))
      (coe v1 v4 v5)
-- Once.CCC.Machine.SMCore.MemOps.clear-frame-just
d_clear'45'frame'45'just_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_742 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem-aux
d_writeHeapMem'45'aux_794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_794 ~v0 ~v1 ~v2 v3 v4 v5
  = du_writeHeapMem'45'aux_794 v3 v4 v5
du_writeHeapMem'45'aux_794 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_794 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeHeapMem
d_writeHeapMem_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_writeHeapMem_800 ~v0 v1 v2 v3 v4
  = du_writeHeapMem_800 v1 v2 v3 v4
du_writeHeapMem_800 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
du_writeHeapMem_800 v0 v1 v2 v3
  = coe
      du_writeHeapMem'45'aux_794
      (coe
         MAlonzo.Code.Once.Memory.HeapAddress.d__'8799'HL__72 (coe v1)
         (coe v3))
      (coe v0 v3) (coe v2)
-- Once.CCC.Machine.SMCore.MemOps.writeLocToStack
d_writeLocToStack_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_408
d_writeLocToStack_810 v0 v1 v2 v3 v4
  = coe
      C_mkLocState_432 (coe d_regs_422 (coe v1))
      (coe
         d_writeStackMem_690 (coe v0) (coe d_stackMem_424 (coe v1)) (coe v2)
         (coe v3) (coe v4))
      (coe d_heapMem_426 (coe v1)) (coe d_halted_428 (coe v1))
      (coe d_ev'45'log_430 (coe v1))
-- Once.CCC.Machine.SMCore.MemOps.writeLocToHeap
d_writeLocToHeap_820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLocToHeap_820 ~v0 v1 v2 v3 = du_writeLocToHeap_820 v1 v2 v3
du_writeLocToHeap_820 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
du_writeLocToHeap_820 v0 v1 v2
  = coe
      C_mkLocState_432 (coe d_regs_422 (coe v0))
      (coe d_stackMem_424 (coe v0))
      (coe
         du_writeHeapMem_800 (coe d_heapMem_426 (coe v0)) (coe v1) (coe v2))
      (coe d_halted_428 (coe v0)) (coe d_ev'45'log_430 (coe v0))
-- Once.CCC.Machine.SMCore.MemOps.writeLoc
d_writeLoc_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLoc_828 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
        -> coe
             d_writeLocToStack_810 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
        -> case coe v3 of
             C_SV'45'Ptr_70 v5
               -> coe
                    seq (coe v5) (coe du_writeLocToHeap_820 (coe v1) (coe v4) (coe v3))
             C_SV'45'Tag_72 v5
               -> coe du_writeLocToHeap_820 (coe v1) (coe v4) (coe v3)
             C_SV'45'Lit_76 v5 v6 v7
               -> coe du_writeLocToHeap_820 (coe v1) (coe v4) (coe v3)
             C_SV'45'Code_78 v5
               -> coe du_writeLocToHeap_820 (coe v1) (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs
d_writeLoc'45'regs_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_878 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-halted
d_writeLoc'45'halted_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_916 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_956 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_956 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_976 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_976 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1004 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1004 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1036 = erased
-- Once.CCC.Machine.SMCore.MemOps.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1314 = erased
-- Once.CCC.Machine.SMCore.LocSourceExt
d_LocSourceExt_1366 a0 = ()
data T_LocSourceExt_1366
  = C_Loc_1370 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 |
    C_IndReg_1372 T_AbstractReg_54 | C_IndRegSuc_1374 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.sv-as-loc
d_sv'45'as'45'loc_1378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_sv'45'as'45'loc_1378 ~v0 v1 = du_sv'45'as'45'loc_1378 v1
du_sv'45'as'45'loc_1378 ::
  T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_sv'45'as'45'loc_1378 v0
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
d_resolveSourceExt_1384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Registers_120 ->
  T_LocSourceExt_1366 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_resolveSourceExt_1384 ~v0 v1 v2 = du_resolveSourceExt_1384 v1 v2
du_resolveSourceExt_1384 ::
  T_Registers_120 ->
  T_LocSourceExt_1366 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_resolveSourceExt_1384 v0 v1
  = case coe v1 of
      C_Loc_1370 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      C_IndReg_1372 v2
        -> coe
             du_sv'45'as'45'loc_1378 (coe du_readReg_144 (coe v0) (coe v2))
      C_IndRegSuc_1374 v2
        -> let v3
                 = coe
                     du_sv'45'as'45'loc_1378 (coe du_readReg_144 (coe v0) (coe v2)) in
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
d_Instr_1414 a0 = ()
data T_Instr_1414
  = C_load_1418 T_AbstractReg_54 T_LocSourceExt_1366 |
    C_store_1420 T_LocSourceExt_1366 T_AbstractReg_54 |
    C_mov_1422 T_AbstractReg_54 T_AbstractReg_54
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame
d_clear'45'frame_1430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_1430 v0 = coe d_clear'45'frame_718 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-aux
d_clear'45'frame'45'aux_1432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_1432 ~v0 = du_clear'45'frame'45'aux_1432
du_clear'45'frame'45'aux_1432 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_1432 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_712 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecFinal._.clear-frame-just
d_clear'45'frame'45'just_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1434 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.readHeapLoc
d_readHeapLoc_1436 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1436 v0 v1 = coe d_heapMem_426 v0 v1
-- Once.CCC.Machine.SMCore.ExecFinal._.readLoc
d_readLoc_1438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1438 ~v0 = du_readLoc_1438
du_readLoc_1438 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1438 = coe du_readLoc_662
-- Once.CCC.Machine.SMCore.ExecFinal._.readStackLoc
d_readStackLoc_1440 ::
  T_LocState_408 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1440 v0 v1 v2 = coe d_stackMem_424 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem
d_writeHeapMem_1442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1442 ~v0 = du_writeHeapMem_1442
du_writeHeapMem_1442 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1442 = coe du_writeHeapMem_800
-- Once.CCC.Machine.SMCore.ExecFinal._.writeHeapMem-aux
d_writeHeapMem'45'aux_1444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1444 ~v0 = du_writeHeapMem'45'aux_1444
du_writeHeapMem'45'aux_1444 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1444 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_794 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc
d_writeLoc_1446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLoc_1446 v0 = coe d_writeLoc_828 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-halted
d_writeLoc'45'halted_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1448 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1450 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1450 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1452 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1452 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1454 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1456 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1456 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs
d_writeLoc'45'regs_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1458 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1460 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1460 = erased
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToHeap
d_writeLocToHeap_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLocToHeap_1462 ~v0 = du_writeLocToHeap_1462
du_writeLocToHeap_1462 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
du_writeLocToHeap_1462 = coe du_writeLocToHeap_820
-- Once.CCC.Machine.SMCore.ExecFinal._.writeLocToStack
d_writeLocToStack_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_408
d_writeLocToStack_1464 v0 = coe d_writeLocToStack_810 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem
d_writeStackMem_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1466 v0 = coe d_writeStackMem_690 (coe v0)
-- Once.CCC.Machine.SMCore.ExecFinal._.writeStackMem-aux
d_writeStackMem'45'aux_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1468 ~v0 = du_writeStackMem'45'aux_1468
du_writeStackMem'45'aux_1468 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1468 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_682 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-with-value
d_exec'45'load'45'with'45'value_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'load'45'with'45'value_1470 ~v0 v1 v2
  = du_exec'45'load'45'with'45'value_1470 v1 v2
du_exec'45'load'45'with'45'value_1470 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
du_exec'45'load'45'with'45'value_1470 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkLocState_432 (coe du_writeReg_156 (d_regs_422 (coe v3)) v0 v2)
                  (coe d_stackMem_424 (coe v3)) (coe d_heapMem_426 (coe v3))
                  (coe d_halted_428 (coe v3)) (coe d_ev'45'log_430 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_432 (coe d_regs_422 (coe v2))
                  (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_430 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
d_exec'45'load'45'via'45'resolved_1482 ~v0 v1 v2
  = du_exec'45'load'45'via'45'resolved_1482 v1 v2
du_exec'45'load'45'via'45'resolved_1482 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
du_exec'45'load'45'via'45'resolved_1482 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1470 v0
                  (coe du_readLoc_662 (coe v3) (coe v2)) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_432 (coe d_regs_422 (coe v2))
                  (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_430 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'store'45'via'45'resolved_1494 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 -> d_writeLoc_828 (coe v0) (coe v4) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_432 (coe d_regs_422 (coe v3))
                  (coe d_stackMem_424 (coe v3)) (coe d_heapMem_426 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_430 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.slot-base
d_slot'45'base_1504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1504 ~v0 v1 = du_slot'45'base_1504 v1
du_slot'45'base_1504 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1504 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'as'45'loc_1378 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_408 -> T_LocState_408
d_exec'45'lea'45'indexed'45'via_1508 ~v0 v1
  = du_exec'45'lea'45'indexed'45'via_1508 v1
du_exec'45'lea'45'indexed'45'via_1508 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_408 -> T_LocState_408
du_exec'45'lea'45'indexed'45'via_1508 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_432
                  (coe
                     du_writeReg_156 (d_regs_422 (coe v3)) (coe C_Input1_56)
                     (coe C_SV'45'Ptr_70 (coe du_offsetLoc_92 (coe v1) (coe v2))))
                  (coe d_stackMem_424 (coe v3)) (coe d_heapMem_426 (coe v3))
                  (coe d_halted_428 (coe v3)) (coe d_ev'45'log_430 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 ->
                coe
                  C_mkLocState_432 (coe d_regs_422 (coe v2))
                  (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_430 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
d_exec'45'load'45'suc'45'via'45'resolved_1520 ~v0 v1 v2
  = du_exec'45'load'45'suc'45'via'45'resolved_1520 v1 v2
du_exec'45'load'45'suc'45'via'45'resolved_1520 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
du_exec'45'load'45'suc'45'via'45'resolved_1520 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  du_exec'45'load'45'with'45'value_1470 v0
                  (coe du_readLoc_662 (coe v3) (coe du_sucLoc_82 (coe v2))) v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 ->
                coe
                  C_mkLocState_432 (coe d_regs_422 (coe v2))
                  (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_430 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'store'45'suc'45'via'45'resolved_1532 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 ->
                d_writeLoc_828
                  (coe v0) (coe v4) (coe du_sucLoc_82 (coe v2)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 ->
                coe
                  C_mkLocState_432 (coe d_regs_422 (coe v3))
                  (coe d_stackMem_424 (coe v3)) (coe d_heapMem_426 (coe v3))
                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                  (coe d_ev'45'log_430 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec
d_exec_1542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1414 -> T_LocState_408 -> T_LocState_408
d_exec_1542 v0 v1
  = case coe v1 of
      C_load_1418 v2 v3
        -> coe
             (\ v4 ->
                coe
                  du_exec'45'load'45'via'45'resolved_1482 v2
                  (coe du_resolveSourceExt_1384 (coe d_regs_422 (coe v4)) (coe v3))
                  v4)
      C_store_1420 v2 v3
        -> coe
             (\ v4 ->
                coe
                  d_exec'45'store'45'via'45'resolved_1494 v0
                  (coe du_resolveSourceExt_1384 (coe d_regs_422 (coe v4)) (coe v2))
                  (coe du_readReg_144 (coe d_regs_422 (coe v4)) (coe v3)) v4)
      C_mov_1422 v2 v3
        -> coe
             (\ v4 ->
                coe
                  C_mkLocState_432
                  (coe
                     du_writeReg_156 (d_regs_422 (coe v4)) v2
                     (coe du_readReg_144 (coe d_regs_422 (coe v4)) (coe v3)))
                  (coe d_stackMem_424 (coe v4)) (coe d_heapMem_426 (coe v4))
                  (coe d_halted_428 (coe v4)) (coe d_ev'45'log_430 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-just
d_exec'45'load'45'just_1568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1568 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.exec-load-nothing
d_exec'45'load'45'nothing_1574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1574 = erased
-- Once.CCC.Machine.SMCore.ExecFinal.execList
d_execList_1576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1414] -> T_LocState_408 -> T_LocState_408
d_execList_1576 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> let v5 = d_halted_428 (coe v2) in
           coe
             (if coe v5
                then coe v2
                else coe
                       d_execList_1576 (coe v0) (coe v4) (coe d_exec_1542 v0 v3 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame
d_clear'45'frame_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_1608 v0 = coe d_clear'45'frame_718 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-aux
d_clear'45'frame'45'aux_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_1610 ~v0 = du_clear'45'frame'45'aux_1610
du_clear'45'frame'45'aux_1610 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_1610 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_712 v4 v5 v6
-- Once.CCC.Machine.SMCore.ExecLemmas._.clear-frame-just
d_clear'45'frame'45'just_1612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_1612 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.readHeapLoc
d_readHeapLoc_1614 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_readHeapLoc_1614 v0 v1 = coe d_heapMem_426 v0 v1
-- Once.CCC.Machine.SMCore.ExecLemmas._.readLoc
d_readLoc_1616 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_1616 ~v0 = du_readLoc_1616
du_readLoc_1616 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_1616 = coe du_readLoc_662
-- Once.CCC.Machine.SMCore.ExecLemmas._.readStackLoc
d_readStackLoc_1618 ::
  T_LocState_408 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_1618 v0 v1 v2 = coe d_stackMem_424 v0 v1 v2
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem
d_writeHeapMem_1620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_writeHeapMem_1620 ~v0 = du_writeHeapMem_1620
du_writeHeapMem_1620 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
du_writeHeapMem_1620 = coe du_writeHeapMem_800
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeHeapMem-aux
d_writeHeapMem'45'aux_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_1622 ~v0 = du_writeHeapMem'45'aux_1622
du_writeHeapMem'45'aux_1622 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_1622 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_794 v2 v3 v4
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc
d_writeLoc_1624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLoc_1624 v0 = coe d_writeLoc_828 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-halted
d_writeLoc'45'halted_1626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_1626 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_1628 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_1628 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_1630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_1630 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_1632 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_1634 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs
d_writeLoc'45'regs_1636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_1636 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_1638 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_1638 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToHeap
d_writeLocToHeap_1640 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLocToHeap_1640 ~v0 = du_writeLocToHeap_1640
du_writeLocToHeap_1640 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
du_writeLocToHeap_1640 = coe du_writeLocToHeap_820
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeLocToStack
d_writeLocToStack_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_408
d_writeLocToStack_1642 v0 = coe d_writeLocToStack_810 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem
d_writeStackMem_1644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_1644 v0 = coe d_writeStackMem_690 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.writeStackMem-aux
d_writeStackMem'45'aux_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_1646 ~v0 = du_writeStackMem'45'aux_1646
du_writeStackMem'45'aux_1646 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_1646 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_682 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec
d_exec_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1414 -> T_LocState_408 -> T_LocState_408
d_exec_1650 v0 = coe d_exec_1542 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_408 -> T_LocState_408
d_exec'45'lea'45'indexed'45'via_1652 ~v0
  = du_exec'45'lea'45'indexed'45'via_1652
du_exec'45'lea'45'indexed'45'via_1652 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_408 -> T_LocState_408
du_exec'45'lea'45'indexed'45'via_1652
  = coe du_exec'45'lea'45'indexed'45'via_1508
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-just
d_exec'45'load'45'just_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_1654 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-nothing
d_exec'45'load'45'nothing_1656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_1656 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_1658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
d_exec'45'load'45'suc'45'via'45'resolved_1658 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_1658
du_exec'45'load'45'suc'45'via'45'resolved_1658 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
du_exec'45'load'45'suc'45'via'45'resolved_1658
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1520
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_1660 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
d_exec'45'load'45'via'45'resolved_1660 ~v0
  = du_exec'45'load'45'via'45'resolved_1660
du_exec'45'load'45'via'45'resolved_1660 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
du_exec'45'load'45'via'45'resolved_1660
  = coe du_exec'45'load'45'via'45'resolved_1482
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-load-with-value
d_exec'45'load'45'with'45'value_1662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'load'45'with'45'value_1662 ~v0
  = du_exec'45'load'45'with'45'value_1662
du_exec'45'load'45'with'45'value_1662 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
du_exec'45'load'45'with'45'value_1662
  = coe du_exec'45'load'45'with'45'value_1470
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_1664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'store'45'suc'45'via'45'resolved_1664 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1532 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_1666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'store'45'via'45'resolved_1666 v0
  = coe d_exec'45'store'45'via'45'resolved_1494 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.execList
d_execList_1668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1414] -> T_LocState_408 -> T_LocState_408
d_execList_1668 v0 = coe d_execList_1576 (coe v0)
-- Once.CCC.Machine.SMCore.ExecLemmas._.slot-base
d_slot'45'base_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_1670 ~v0 = du_slot'45'base_1670
du_slot'45'base_1670 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_1670 = coe du_slot'45'base_1504
-- Once.CCC.Machine.SMCore.ExecLemmas.resolved-readLoc
d_resolved'45'readLoc_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 -> T_LocSourceExt_1366 -> Maybe T_StoredValue_66
d_resolved'45'readLoc_1672 ~v0 v1 v2
  = du_resolved'45'readLoc_1672 v1 v2
du_resolved'45'readLoc_1672 ::
  T_LocState_408 -> T_LocSourceExt_1366 -> Maybe T_StoredValue_66
du_resolved'45'readLoc_1672 v0 v1
  = let v2
          = coe
              du_resolveSourceExt_1384 (coe d_regs_422 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe du_readLoc_662 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.ExecLemmas.load-result
d_load'45'result_1702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'result_1702 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-reg
d_load'45'preserves'45'reg_1772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'reg_1772 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-resolve-preserves
d_load'45'failed'45'resolve'45'preserves_1848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'resolve'45'preserves_1848 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-failed-read-preserves
d_load'45'failed'45'read'45'preserves_1878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'failed'45'read'45'preserves_1878 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-stackMem
d_load'45'preserves'45'stackMem_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'stackMem_1934 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-heapMem
d_load'45'preserves'45'heapMem_1986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'heapMem_1986 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-result
d_mov'45'result_2038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'result_2038 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-reg
d_mov'45'preserves'45'reg_2054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_408 ->
  T_AbstractReg_54 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'reg_2054 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-stackMem
d_mov'45'preserves'45'stackMem_2072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'stackMem_2072 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.mov-preserves-heapMem
d_mov'45'preserves'45'heapMem_2086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_AbstractReg_54 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mov'45'preserves'45'heapMem_2086 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-preserves-halted
d_load'45'preserves'45'halted_2104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'preserves'45'halted_2104 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.load-no-halt
d_load'45'no'45'halt_2170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocSourceExt_1366 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_load'45'no'45'halt_2170 = erased
-- Once.CCC.Machine.SMCore.ExecLemmas.readLoc-stackMem-eq
d_readLoc'45'stackMem'45'eq_2194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readLoc'45'stackMem'45'eq_2194 = erased
-- Once.CCC.Machine.SMCore.FlatCtrl
d_FlatCtrl_2222 = ()
data T_FlatCtrl_2222
  = C_c'45'label_2224 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'jmp_2226 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'scratch'45'zero_2228 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'branch'45'tag'45'zero_2230 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_c'45'entry_2232 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                      Integer |
    C_c'45'ret_2234 Integer |
    C_c'45'call'45'fn_2236 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_c'45'start_2238 Integer
-- Once.CCC.Machine.SMCore.AbstractInstr
d_AbstractInstr_2246 = ()
data T_AbstractInstr_2246
  = C_mov'45'to'45'output_2248 | C_mov'45'to'45'input_2250 |
    C_load'45'indirect_2252 | C_load'45'indirect'45'suc_2254 |
    C_load'45'from'45'slot_2256 Integer |
    C_store'45'at'45'slot_2258 Integer | C_store'45'indirect_2260 |
    C_store'45'indirect'45'suc_2262 | C_lea'45'slot_2264 Integer |
    C_restore'45'input_2266 Integer |
    C_instr'45'alloc'45'stack_2268 Integer |
    C_instr'45'dealloc'45'stack_2270 Integer |
    C_instr'45'reclaim'45'to_2272 Integer |
    C_instr'45'push'45'frame_2274 Integer |
    C_instr'45'pop'45'frame_2276 | C_instr'45'call'45'closure_2278 |
    C_worklist'45'init_2280 Integer | C_worklist'45'push_2282 Integer |
    C_worklist'45'pop_2284 Integer | C_worklist'45'check_2286 Integer |
    C_instr'45'sigop_2292 MAlonzo.Code.Once.Spec.Type.T_Type_8
                          MAlonzo.Code.Once.Spec.Type.T_Type_8
                          MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 |
    C_instr'45'load'45'const_2298 MAlonzo.Code.Once.Spec.Type.T_Type_8
                                  MAlonzo.Code.Once.Type.T_FitsInReg_56 AgdaAny |
    C_instr'45'load'45'code'45'addr_2300 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_instr'45'save'45'closure'45'reg_2302 |
    C_instr'45'load'45'tag'45'lit_2304 Integer |
    C_instr'45'case'45'on'45'tag_2306 [T_AbstractInstr_2246]
                                      [T_AbstractInstr_2246] |
    C_instr'45'alloc'45'heap_2308 Integer |
    C_instr'45'loop_2310 [T_AbstractInstr_2246] |
    C_instr'45'reg'45'op_2312 T_RegOp_364 |
    C_instr'45'ctrl_2314 T_FlatCtrl_2222 |
    C_lea'45'indexed_2316 Integer
-- Once.CCC.Machine.SMCore.CallI
d_CallI_2318 :: T_AbstractInstr_2246 -> ()
d_CallI_2318 = erased
-- Once.CCC.Machine.SMCore.AbstractTrace
d_AbstractTrace_2320 :: ()
d_AbstractTrace_2320 = erased
-- Once.CCC.Machine.SMCore.CompUnit
d_CompUnit_2322 = ()
data T_CompUnit_2322
  = C_unit_2336 Integer [T_AbstractInstr_2246]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Machine.SMCore.CompUnit.entry-budget
d_entry'45'budget_2330 :: T_CompUnit_2322 -> Integer
d_entry'45'budget_2330 v0
  = case coe v0 of
      C_unit_2336 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.entry
d_entry_2332 :: T_CompUnit_2322 -> [T_AbstractInstr_2246]
d_entry_2332 v0
  = case coe v0 of
      C_unit_2336 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.CompUnit.blocks
d_blocks_2334 ::
  T_CompUnit_2322 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks_2334 v0
  = case coe v0 of
      C_unit_2336 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.block-layout
d_block'45'layout_2338 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_AbstractInstr_2246]
d_block'45'layout_2338 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       C_instr'45'ctrl_2314
                       (coe
                          C_c'45'entry_2232
                          (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v1))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe C_instr'45'ctrl_2314 (coe C_c'45'ret_2234 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout
d_blocks'45'layout_2346 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_AbstractInstr_2246]
d_blocks'45'layout_2346 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_block'45'layout_2338 (coe v1))
             (coe d_blocks'45'layout_2346 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.blocks-layout-++
d_blocks'45'layout'45''43''43'_2356 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_blocks'45'layout'45''43''43'_2356 = erased
-- Once.CCC.Machine.SMCore.link
d_link_2368 :: T_CompUnit_2322 -> [T_AbstractInstr_2246]
d_link_2368 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2332 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2314
            (coe C_c'45'ret_2234 (coe d_entry'45'budget_2330 (coe v0))))
         (coe d_blocks'45'layout_2346 (coe d_blocks_2334 (coe v0))))
-- Once.CCC.Machine.SMCore.link-top
d_link'45'top_2372 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  T_CompUnit_2322 -> [T_AbstractInstr_2246]
d_link'45'top_2372 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2332 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe C_instr'45'ctrl_2314 (coe C_c'45'label_2224 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe C_instr'45'ctrl_2314 (coe C_c'45'jmp_2226 (coe v0)))
            (coe d_blocks'45'layout_2346 (coe d_blocks_2334 (coe v1)))))
-- Once.CCC.Machine.SMCore.link-pre
d_link'45'pre_2378 ::
  T_CompUnit_2322 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> [T_AbstractInstr_2246]
d_link'45'pre_2378 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_entry_2332 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            C_instr'45'ctrl_2314
            (coe C_c'45'ret_2234 (coe d_entry'45'budget_2330 (coe v0))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_blocks'45'layout_2346 (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  C_instr'45'ctrl_2314
                  (coe
                     C_c'45'entry_2232
                     (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2))
                     (coe v3)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.CCC.Machine.SMCore.link-post
d_link'45'post_2388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [T_AbstractInstr_2246]
d_link'45'post_2388 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_instr'45'ctrl_2314 (coe C_c'45'ret_2234 (coe v1)))
      (coe d_blocks'45'layout_2346 (coe v0))
-- Once.CCC.Machine.SMCore.link-block-split
d_link'45'block'45'split_2406 ::
  T_CompUnit_2322 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2246] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_link'45'block'45'split_2406 = erased
-- Once.CCC.Machine.SMCore._.inner
d_inner_2426 ::
  T_CompUnit_2322 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_AbstractInstr_2246] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inner_2426 = erased
-- Once.CCC.Machine.SMCore.TreeTrace
d_TreeTrace_2434 = ()
data T_TreeTrace_2434
  = C_ε_2436 | C_instr_2438 T_AbstractInstr_2246 |
    C__'9656'__2440 T_TreeTrace_2434 T_TreeTrace_2434 |
    C_branch_2442 Integer T_TreeTrace_2434 T_TreeTrace_2434 |
    C_call'45'sub_2444 T_TreeTrace_2434 |
    C_flat_2446 [T_AbstractInstr_2246]
-- Once.CCC.Machine.SMCore.flatToTree
d_flatToTree_2448 :: [T_AbstractInstr_2246] -> T_TreeTrace_2434
d_flatToTree_2448 v0
  = case coe v0 of
      [] -> coe C_ε_2436
      (:) v1 v2
        -> coe
             C__'9656'__2440 (coe C_instr_2438 (coe v1))
             (coe d_flatToTree_2448 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToFlat
d_treeToFlat_2454 :: T_TreeTrace_2434 -> [T_AbstractInstr_2246]
d_treeToFlat_2454 v0
  = case coe v0 of
      C_ε_2436 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2438 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2440 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2454 (coe v1)) (coe d_treeToFlat_2454 (coe v2))
      C_branch_2442 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToFlat_2454 (coe v2)) (coe d_treeToFlat_2454 (coe v3))
      C_call'45'sub_2444 v1 -> coe d_treeToFlat_2454 (coe v1)
      C_flat_2446 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnable
d_treeToRunnable_2470 ::
  Integer -> T_TreeTrace_2434 -> [T_AbstractInstr_2246]
d_treeToRunnable_2470 v0 v1
  = case coe v1 of
      C_ε_2436 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_instr_2438 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C__'9656'__2440 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2470 (coe v0) (coe v2))
             (coe d_treeToRunnable_2470 (coe v0) (coe v3))
      C_branch_2442 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_treeToRunnable_2470 (coe v0) (coe v3))
             (coe d_treeToRunnable_2470 (coe v0) (coe v4))
      C_call'45'sub_2444 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_worklist'45'push_2282 (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_treeToRunnable_2470 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_worklist'45'pop_2284 (coe v0))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_2446 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.treeToRunnableWithInit
d_treeToRunnableWithInit_2500 ::
  Integer -> T_TreeTrace_2434 -> [T_AbstractInstr_2246]
d_treeToRunnableWithInit_2500 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe C_worklist'45'init_2280 (coe v0))
      (coe d_treeToRunnable_2470 (coe v0) (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame
d_clear'45'frame_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny -> Integer -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_clear'45'frame_2550 v0 = coe d_clear'45'frame_718 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-aux
d_clear'45'frame'45'aux_2552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
d_clear'45'frame'45'aux_2552 ~v0 = du_clear'45'frame'45'aux_2552
du_clear'45'frame'45'aux_2552 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 -> Maybe T_StoredValue_66
du_clear'45'frame'45'aux_2552 v0 v1 v2 v3 v4 v5 v6
  = coe du_clear'45'frame'45'aux_712 v4 v5 v6
-- Once.CCC.Machine.SMCore.AbstractExec._.clear-frame-just
d_clear'45'frame'45'just_2554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clear'45'frame'45'just_2554 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.readHeapLoc
d_readHeapLoc_2556 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_readHeapLoc_2556 v0 v1 = coe d_heapMem_426 v0 v1
-- Once.CCC.Machine.SMCore.AbstractExec._.readLoc
d_readLoc_2558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
d_readLoc_2558 ~v0 = du_readLoc_2558
du_readLoc_2558 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe T_StoredValue_66
du_readLoc_2558 = coe du_readLoc_662
-- Once.CCC.Machine.SMCore.AbstractExec._.readStackLoc
d_readStackLoc_2560 ::
  T_LocState_408 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_readStackLoc_2560 v0 v1 v2 = coe d_stackMem_424 v0 v1 v2
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem
d_writeHeapMem_2562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
d_writeHeapMem_2562 ~v0 = du_writeHeapMem_2562
du_writeHeapMem_2562 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
   Maybe T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  Maybe T_StoredValue_66
du_writeHeapMem_2562 = coe du_writeHeapMem_800
-- Once.CCC.Machine.SMCore.AbstractExec._.writeHeapMem-aux
d_writeHeapMem'45'aux_2564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeHeapMem'45'aux_2564 ~v0 = du_writeHeapMem'45'aux_2564
du_writeHeapMem'45'aux_2564 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeHeapMem'45'aux_2564 v0 v1 v2 v3 v4
  = coe du_writeHeapMem'45'aux_794 v2 v3 v4
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc
d_writeLoc_2566 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLoc_2566 v0 = coe d_writeLoc_828 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-halted
d_writeLoc'45'halted_2568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'halted_2568 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-heapMem-stack
d_writeLoc'45'heapMem'45'stack_2570 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'heapMem'45'stack_2570 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other
d_writeLoc'45'preserves'45'other_2572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other_2572 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-preserves-other-stack-aux
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_LocState_408 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'preserves'45'other'45'stack'45'aux_2574 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-read-same-stack
d_writeLoc'45'read'45'same'45'stack_2576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'read'45'same'45'stack_2576 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs
d_writeLoc'45'regs_2578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs_2578 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLoc-regs-commute
d_writeLoc'45'regs'45'commute_2580 ::
  T_LocState_408 ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 ->
  T_Registers_120 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_writeLoc'45'regs'45'commute_2580 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToHeap
d_writeLocToHeap_2582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
d_writeLocToHeap_2582 ~v0 = du_writeLocToHeap_2582
du_writeLocToHeap_2582 ::
  T_LocState_408 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_StoredValue_66 -> T_LocState_408
du_writeLocToHeap_2582 = coe du_writeLocToHeap_820
-- Once.CCC.Machine.SMCore.AbstractExec._.writeLocToStack
d_writeLocToStack_2584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 ->
  AgdaAny -> Integer -> T_StoredValue_66 -> T_LocState_408
d_writeLocToStack_2584 v0 = coe d_writeLocToStack_810 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem
d_writeStackMem_2586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (AgdaAny -> Integer -> Maybe T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  T_StoredValue_66 -> AgdaAny -> Integer -> Maybe T_StoredValue_66
d_writeStackMem_2586 v0 = coe d_writeStackMem_690 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.writeStackMem-aux
d_writeStackMem'45'aux_2588 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
d_writeStackMem'45'aux_2588 ~v0 = du_writeStackMem'45'aux_2588
du_writeStackMem'45'aux_2588 ::
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_StoredValue_66 ->
  T_StoredValue_66 -> Maybe T_StoredValue_66
du_writeStackMem'45'aux_2588 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du_writeStackMem'45'aux_682 v4 v5 v6 v7
-- Once.CCC.Machine.SMCore.AbstractExec._.exec
d_exec_2592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_Instr_1414 -> T_LocState_408 -> T_LocState_408
d_exec_2592 v0 = coe d_exec_1542 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-lea-indexed-via
d_exec'45'lea'45'indexed'45'via_2594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_408 -> T_LocState_408
d_exec'45'lea'45'indexed'45'via_2594 ~v0
  = du_exec'45'lea'45'indexed'45'via_2594
du_exec'45'lea'45'indexed'45'via_2594 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Integer -> T_LocState_408 -> T_LocState_408
du_exec'45'lea'45'indexed'45'via_2594
  = coe du_exec'45'lea'45'indexed'45'via_1508
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-just
d_exec'45'load'45'just_2596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_StoredValue_66 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'just_2596 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-nothing
d_exec'45'load'45'nothing_2598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  T_LocState_408 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'nothing_2598 = erased
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_2600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
d_exec'45'load'45'suc'45'via'45'resolved_2600 ~v0
  = du_exec'45'load'45'suc'45'via'45'resolved_2600
du_exec'45'load'45'suc'45'via'45'resolved_2600 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
du_exec'45'load'45'suc'45'via'45'resolved_2600
  = coe du_exec'45'load'45'suc'45'via'45'resolved_1520
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_2602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
d_exec'45'load'45'via'45'resolved_2602 ~v0
  = du_exec'45'load'45'via'45'resolved_2602
du_exec'45'load'45'via'45'resolved_2602 ::
  T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> T_LocState_408
du_exec'45'load'45'via'45'resolved_2602
  = coe du_exec'45'load'45'via'45'resolved_1482
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-load-with-value
d_exec'45'load'45'with'45'value_2604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'load'45'with'45'value_2604 ~v0
  = du_exec'45'load'45'with'45'value_2604
du_exec'45'load'45'with'45'value_2604 ::
  T_AbstractReg_54 ->
  Maybe T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
du_exec'45'load'45'with'45'value_2604
  = coe du_exec'45'load'45'with'45'value_1470
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_2606 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'store'45'suc'45'via'45'resolved_2606 v0
  = coe d_exec'45'store'45'suc'45'via'45'resolved_1532 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_2608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66 -> T_LocState_408 -> T_LocState_408
d_exec'45'store'45'via'45'resolved_2608 v0
  = coe d_exec'45'store'45'via'45'resolved_1494 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.execList
d_execList_2610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_Instr_1414] -> T_LocState_408 -> T_LocState_408
d_execList_2610 v0 = coe d_execList_1576 (coe v0)
-- Once.CCC.Machine.SMCore.AbstractExec._.slot-base
d_slot'45'base_2612 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
d_slot'45'base_2612 ~v0 = du_slot'45'base_2612
du_slot'45'base_2612 ::
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
du_slot'45'base_2612 = coe du_slot'45'base_1504
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-with-value
d_exec'45'load'45'from'45'slot'45'with'45'value_2614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'load'45'from'45'slot'45'with'45'value_2614 ~v0 v1 v2 v3
  = du_exec'45'load'45'from'45'slot'45'with'45'value_2614 v1 v2 v3
du_exec'45'load'45'from'45'slot'45'with'45'value_2614 ::
  Maybe T_StoredValue_66 ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'load'45'from'45'slot'45'with'45'value_2614 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe du_writeReg_156 (d_regs_422 (coe v1)) (coe C_Output_58) v3)
                (coe d_stackMem_424 (coe v1)) (coe d_heapMem_426 (coe v1))
                (coe d_halted_428 (coe v1)) (coe d_ev'45'log_430 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432 (coe d_regs_422 (coe v1))
                (coe d_stackMem_424 (coe v1)) (coe d_heapMem_426 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_430 (coe v1)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-with-value
d_exec'45'restore'45'input'45'with'45'value_2626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'restore'45'input'45'with'45'value_2626 ~v0 v1 v2 v3
  = du_exec'45'restore'45'input'45'with'45'value_2626 v1 v2 v3
du_exec'45'restore'45'input'45'with'45'value_2626 ::
  Maybe T_StoredValue_66 ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'restore'45'input'45'with'45'value_2626 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe du_writeReg_156 (d_regs_422 (coe v1)) (coe C_Input1_56) v3)
                (coe d_stackMem_424 (coe v1)) (coe d_heapMem_426 (coe v1))
                (coe d_halted_428 (coe v1)) (coe d_ev'45'log_430 (coe v1)))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432 (coe d_regs_422 (coe v1))
                (coe d_stackMem_424 (coe v1)) (coe d_heapMem_426 (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_430 (coe v1)))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-just
d_exec'45'load'45'from'45'slot'45'just_2644 ::
  T_StoredValue_66 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'just_2644 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-load-from-slot-nothing
d_exec'45'load'45'from'45'slot'45'nothing_2650 ::
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'load'45'from'45'slot'45'nothing_2650 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-just
d_exec'45'restore'45'input'45'just_2658 ::
  T_StoredValue_66 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'just_2658 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-restore-input-nothing
d_exec'45'restore'45'input'45'nothing_2664 ::
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'restore'45'input'45'nothing_2664 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.unit-storedvalue
d_unit'45'storedvalue_2666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_StoredValue_66
d_unit'45'storedvalue_2666 ~v0 = du_unit'45'storedvalue_2666
du_unit'45'storedvalue_2666 :: T_StoredValue_66
du_unit'45'storedvalue_2666
  = coe
      C_SV'45'Lit_76 (coe MAlonzo.Code.Once.Spec.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Type.C_fits'45'int_58) (coe (0 :: Integer))
-- Once.CCC.Machine.SMCore.AbstractExec.combine-typed
d_combine'45'typed_2672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'typed_2672 ~v0 ~v1 ~v2 v3 v4
  = du_combine'45'typed_2672 v3 v4
du_combine'45'typed_2672 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'typed_2672 v0 v1
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
d_readTyped'45'int_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 -> Maybe Integer
d_readTyped'45'int_2678 ~v0 v1 = du_readTyped'45'int_2678 v1
du_readTyped'45'int_2678 :: Maybe T_StoredValue_66 -> Maybe Integer
du_readTyped'45'int_2678 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_SV'45'Ptr_70 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Tag_72 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Lit_76 v2 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_fits'45'int_58
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                    MAlonzo.Code.Once.Type.C_fits'45'float_60
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Code_78 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-float
d_readTyped'45'float_2682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 -> Maybe Integer
d_readTyped'45'float_2682 ~v0 v1 = du_readTyped'45'float_2682 v1
du_readTyped'45'float_2682 ::
  Maybe T_StoredValue_66 -> Maybe Integer
du_readTyped'45'float_2682 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_SV'45'Ptr_70 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Tag_72 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_SV'45'Lit_76 v2 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_fits'45'int_58
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.Type.C_fits'45'float_60
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_SV'45'Code_78 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-cell
d_readTyped'45'cell_2688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 -> Maybe AgdaAny
d_readTyped'45'cell_2688 ~v0 ~v1 v2 v3 v4
  = du_readTyped'45'cell_2688 v2 v3 v4
du_readTyped'45'cell_2688 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 -> Maybe AgdaAny
du_readTyped'45'cell_2688 v0 v1 v2
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
d_readTyped'45'pair_2724 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_readTyped'45'pair_2724 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_readTyped'45'pair_2724 v3 v4 v5 v6 v7 v8
du_readTyped'45'pair_2724 ::
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  (T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_readTyped'45'pair_2724 v0 v1 v2 v3 v4 v5
  = coe
      du_combine'45'typed_2672
      (coe du_readTyped'45'cell_2688 (coe v0) (coe v2) (coe v4))
      (coe du_readTyped'45'cell_2688 (coe v1) (coe v3) (coe v5))
-- Once.CCC.Machine.SMCore.AbstractExec.readReg-typed
d_readReg'45'typed_2740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  T_StoredValue_66 -> Maybe AgdaAny
d_readReg'45'typed_2740 ~v0 v1 v2 = du_readReg'45'typed_2740 v1 v2
du_readReg'45'typed_2740 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  T_StoredValue_66 -> Maybe AgdaAny
du_readReg'45'typed_2740 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_20
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C_Int_34
           -> case coe v1 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_58
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         MAlonzo.Code.Once.Spec.Type.C_Float_36
           -> case coe v1 of
                C_SV'45'Lit_76 v3 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_60
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                       _ -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.readTyped-sum
d_readTyped'45'sum_2750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_readTyped'45'sum_2750 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_readTyped'45'sum_2750 v3 v4 v5 v6
du_readTyped'45'sum_2750 ::
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  (Maybe T_StoredValue_66 -> Maybe AgdaAny) ->
  Maybe T_StoredValue_66 ->
  Maybe T_StoredValue_66 ->
  Maybe MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_readTyped'45'sum_2750 v0 v1 v2 v3
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
d_readTyped_2796 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> Maybe AgdaAny
d_readTyped_2796 ~v0 v1 v2 v3 = du_readTyped_2796 v1 v2 v3
du_readTyped_2796 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_LocState_408 -> Maybe AgdaAny
du_readTyped_2796 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_Unit_20
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.C__'42'__24 v4 v5
           -> coe
                du_readTyped'45'pair_2724
                (coe (\ v6 -> coe du_readTyped_2796 (coe v4) (coe v6) (coe v2)))
                (coe (\ v6 -> coe du_readTyped_2796 (coe v5) (coe v6) (coe v2)))
                (coe du_readReg'45'typed_2740 (coe v4))
                (coe du_readReg'45'typed_2740 (coe v5))
                (coe du_readLoc_662 (coe v2) (coe v1))
                (coe du_readLoc_662 (coe v2) (coe du_sucLoc_82 (coe v1)))
         MAlonzo.Code.Once.Spec.Type.C__'43'__26 v4 v5
           -> coe
                du_readTyped'45'sum_2750
                (coe
                   du_readTyped'45'cell_2688
                   (coe (\ v6 -> coe du_readTyped_2796 (coe v4) (coe v6) (coe v2)))
                   (coe du_readReg'45'typed_2740 (coe v4)))
                (coe
                   du_readTyped'45'cell_2688
                   (coe (\ v6 -> coe du_readTyped_2796 (coe v5) (coe v6) (coe v2)))
                   (coe du_readReg'45'typed_2740 (coe v5)))
                (coe du_readLoc_662 (coe v2) (coe v1))
                (coe du_readLoc_662 (coe v2) (coe du_sucLoc_82 (coe v1)))
         MAlonzo.Code.Once.Spec.Type.C_Int_34
           -> coe
                du_readTyped'45'int_2678 (coe du_readLoc_662 (coe v2) (coe v1))
         MAlonzo.Code.Once.Spec.Type.C_Float_36
           -> coe
                du_readTyped'45'float_2682 (coe du_readLoc_662 (coe v2) (coe v1))
         _ -> coe v3)
-- Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output
d_structured'45'pure'45'sigop'45'output_2842
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.CCC.Machine.SMCore.AbstractExec.structured-pure-sigop-output"
-- Once.CCC.Machine.SMCore.AbstractExec.decode-at
d_decode'45'at_2846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  T_StoredValue_66 -> T_LocState_408 -> Maybe AgdaAny
d_decode'45'at_2846 ~v0 v1 v2 v3 v4
  = du_decode'45'at_2846 v1 v2 v3 v4
du_decode'45'at_2846 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  T_StoredValue_66 -> T_LocState_408 -> Maybe AgdaAny
du_decode'45'at_2846 v0 v1 v2 v3
  = let v4
          = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
            coe
              (case coe v2 of
                 C_SV'45'Ptr_70 v5
                   -> coe du_readTyped_2796 (coe v0) (coe v5) (coe v3)
                 _ -> coe v4) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Int_14
           -> case coe v2 of
                C_SV'45'Lit_76 v5 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_58
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Float_16
           -> case coe v2 of
                C_SV'45'Lit_76 v5 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_fits'45'float_60
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.events-at-arg
d_events'45'at'45'arg_2862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_events'45'at'45'arg_2862 ~v0 v1 ~v2 v3 v4
  = du_events'45'at'45'arg_2862 v1 v3 v4
du_events'45'at'45'arg_2862 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe AgdaAny ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_events'45'at'45'arg_2862 v0 v1 v2
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
d_machine'45'events_2876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_machine'45'events_2876 ~v0 v1 ~v2 v3 v4
  = du_machine'45'events_2876 v1 v3 v4
du_machine'45'events_2876 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_machine'45'events_2876 v0 v1 v2
  = coe
      du_events'45'at'45'arg_2862 (coe v0) (coe v1)
      (coe
         du_decode'45'at_2846 (coe v0)
         (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v1))
         (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Input1_56))
         (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans-at
d_call'45'sigop'45'ans'45'at_2888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  Maybe AgdaAny -> T_StoredValue_66
d_call'45'sigop'45'ans'45'at_2888 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             C_SV'45'Lit_76 (coe v2) (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.d_answer_274
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_120 (coe v0))
                (d_ev'45'log_430 (coe v4))
                (coe
                   MAlonzo.Code.Once.Denotation.TraceMonad.C_callOp_142
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v3)) (coe v1)
                   (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3)) (coe v2))
                v6 v8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2666
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-ans
d_call'45'sigop'45'ans_2918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_StoredValue_66
d_call'45'sigop'45'ans_2918 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           d_call'45'sigop'45'ans'45'at_2888 (coe v0) (coe v1) (coe v2)
                           (coe v3) (coe v4) (coe v5) (coe v9)
                           (coe
                              du_decode'45'at_2846 (coe v1)
                              (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3))
                              (coe du_readReg_144 (coe d_regs_422 (coe v4)) (coe C_Input1_56))
                              (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v8) (coe du_unit'45'storedvalue_2666)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-dec
d_call'45'sigop'45'dec_2940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_call'45'sigop'45'dec_2940 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Contract.d__'8712'K'63'__176
      (MAlonzo.Code.Once.Denotation.TraceMonad.d_callKey_246
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.C_callOp_142
            (coe MAlonzo.Code.Once.SigOp.Info.d_name_178 (coe v3)) (coe v1)
            (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v3)) (coe v2)))
      (MAlonzo.Code.Once.Denotation.TraceMonad.d_calls_262
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'interp_120 (coe v0)))
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-val
d_call'45'sigop'45'val_2952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_56 -> T_StoredValue_66
d_call'45'sigop'45'val_2952 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_call'45'sigop'45'ans_2918 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe
                d_call'45'sigop'45'dec_2940 (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2666
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.call-sigop-output
d_call'45'sigop'45'output_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 -> T_StoredValue_66
d_call'45'sigop'45'output_2968 v0 v1 v2 v3 v4
  = coe
      d_call'45'sigop'45'val_2952 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_64 (coe v2))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-output
d_pure'45'sigop'45'output_2980 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 -> T_StoredValue_66
d_pure'45'sigop'45'output_2980 v0 v1 v2 v3 v4
  = coe
      d_pure'45'sigop'45'out'45'aux_3010 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.Type.d_fits'45'in'45'reg'63'_64 (coe v2))
      (coe
         du_sv'45'as'45'loc_1378
         (coe du_readReg_144 (coe d_regs_422 (coe v4)) (coe C_Input1_56)))
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-val
d_pure'45'sigop'45'out'45'val_2986 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 ->
  Maybe AgdaAny -> T_StoredValue_66
d_pure'45'sigop'45'out'45'val_2986 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_res'45'sv_2990 (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Once.SigOp.Info.d_semM_274 v1 v2
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'ffi_154 (coe v0)) v3
                (MAlonzo.Code.Once.CCC.FrameSemantics.d_fs'45'numerics_158
                   (coe v0))
                v6)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_unit'45'storedvalue_2666
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.res-sv
d_res'45'sv_2990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_66
d_res'45'sv_2990 ~v0 v1 v2 v3 = du_res'45'sv_2990 v1 v2 v3
du_res'45'sv_2990 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> T_StoredValue_66
du_res'45'sv_2990 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe du_unit'45'storedvalue_2666
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe C_SV'45'Lit_76 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.pure-sigop-out-aux
d_pure'45'sigop'45'out'45'aux_3010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  Maybe MAlonzo.Code.Once.Type.T_FitsInReg_56 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  T_StoredValue_66
d_pure'45'sigop'45'out'45'aux_3010 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> coe
                    d_pure'45'sigop'45'out'45'val_2986 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe du_readTyped_2796 (coe v1) (coe v8) (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    d_pure'45'sigop'45'out'45'val_2986 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v7)
                    (coe
                       du_readReg'45'typed_2740 (coe v1)
                       (coe du_readReg_144 (coe d_regs_422 (coe v4)) (coe C_Input1_56)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_structured'45'pure'45'sigop'45'output_2842 v0 v1 v2 v3 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output-of
d_exec'45'sigop'45'output'45'of_3046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 -> T_StoredValue_66
d_exec'45'sigop'45'output'45'of_3046 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe
             d_pure'45'sigop'45'output_2980 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe du_unit'45'storedvalue_2666
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe du_unit'45'storedvalue_2666
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe
             d_call'45'sigop'45'output_2968 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events-of
d_sigop'45'events'45'of_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events'45'of_3060 ~v0 v1 ~v2 v3 v4 v5
  = du_sigop'45'events'45'of_3060 v1 v3 v4 v5
du_sigop'45'events'45'of_3060 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events'45'of_3060 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe du_machine'45'events_2876 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe du_machine'45'events_2876 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe du_machine'45'events_2876 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.sigop-events
d_sigop'45'events_3078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_sigop'45'events_3078 ~v0 v1 ~v2 v3 v4
  = du_sigop'45'events_3078 v1 v3 v4
du_sigop'45'events_3078 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
du_sigop'45'events_3078 v0 v1 v2
  = coe
      du_sigop'45'events'45'of_3060 (coe v0)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_284 (coe v1)) (coe v1)
      (coe v2)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-output
d_exec'45'sigop'45'output_3088 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 -> T_StoredValue_66
d_exec'45'sigop'45'output_3088 v0 v1 v2 v3 v4
  = coe
      d_exec'45'sigop'45'output'45'of_3046 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_284 (coe v3)) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts-of
d_exec'45'sigop'45'halts'45'of_3098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 -> Bool
d_exec'45'sigop'45'halts'45'of_3098 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_exec'45'sigop'45'halts'45'of_3098 v3
du_exec'45'sigop'45'halts'45'of_3098 ::
  MAlonzo.Code.Once.SigOp.Info.T_EffectShape_126 -> Bool
du_exec'45'sigop'45'halts'45'of_3098 v0
  = case coe v0 of
      MAlonzo.Code.Once.SigOp.Info.C_Pure_130
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Emits_132
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.SigOp.Info.C_Halts_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.SigOp.Info.C_Answers_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-sigop-halts
d_exec'45'sigop'45'halts_3104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  T_LocState_408 -> Bool
d_exec'45'sigop'45'halts_3104 ~v0 ~v1 ~v2 v3 ~v4
  = du_exec'45'sigop'45'halts_3104 v3
du_exec'45'sigop'45'halts_3104 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> Bool
du_exec'45'sigop'45'halts_3104 v0
  = coe
      du_exec'45'sigop'45'halts'45'of_3098
      (coe MAlonzo.Code.Once.SigOp.Info.du_effect_284 (coe v0))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-fuel
d_loop'45'fuel_3110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> Integer
d_loop'45'fuel_3110 ~v0 = du_loop'45'fuel_3110
du_loop'45'fuel_3110 :: Integer
du_loop'45'fuel_3110 = coe (1000000 :: Integer)
-- Once.CCC.Machine.SMCore.AbstractExec.case-tag-at
d_case'45'tag'45'at_3112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 -> Maybe T_StoredValue_66
d_case'45'tag'45'at_3112 ~v0 v1 = du_case'45'tag'45'at_3112 v1
du_case'45'tag'45'at_3112 ::
  T_LocState_408 -> Maybe T_StoredValue_66
du_case'45'tag'45'at_3112 v0
  = let v1
          = coe
              du_sv'45'as'45'loc_1378
              (coe d_input1_132 (coe d_regs_422 (coe v0))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe du_readLoc_662 (coe v0) (coe v2)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.BodyRunner
d_BodyRunner_3126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 -> ()
d_BodyRunner_3126 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-loc
d_loop'45'reanchor'45'loc_3128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 -> T_LocState_408 -> T_LocState_408
d_loop'45'reanchor'45'loc_3128 ~v0 v1 v2
  = du_loop'45'reanchor'45'loc_3128 v1 v2
du_loop'45'reanchor'45'loc_3128 ::
  T_LocState_408 -> T_LocState_408 -> T_LocState_408
du_loop'45'reanchor'45'loc_3128 v0 v1
  = coe
      C_mkLocState_432 (coe d_regs_422 (coe v1))
      (coe d_stackMem_424 (coe v0)) (coe d_heapMem_426 (coe v1))
      (coe d_halted_428 (coe v1)) (coe d_ev'45'log_430 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.loop-reanchor-alloc
d_loop'45'reanchor'45'alloc_3134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AllocState_500 -> T_AllocState_500 -> T_AllocState_500
d_loop'45'reanchor'45'alloc_3134 ~v0 v1 v2
  = du_loop'45'reanchor'45'alloc_3134 v1 v2
du_loop'45'reanchor'45'alloc_3134 ::
  T_AllocState_500 -> T_AllocState_500 -> T_AllocState_500
du_loop'45'reanchor'45'alloc_3134 v0 v1
  = coe
      C_mkAllocState_604 (coe d_current'45'frame_592 (coe v0))
      (coe d_saved'45'frames_594 (coe v1))
      (coe d_frame'45'slots_596 (coe v1))
      (coe d_next'45'slot_598 (coe v0))
      (coe d_next'45'heap'45'ref_600 (coe v1))
      (coe d_block'45'size_602 (coe v1))
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop-run
d_exec'45'loop'45'run_3140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_LocState_408 ->
   T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop'45'run_3140 ~v0 v1 v2 v3 v4
  = du_exec'45'loop'45'run_3140 v1 v2 v3 v4
du_exec'45'loop'45'run_3140 ::
  (T_LocState_408 ->
   T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'loop'45'run_3140 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432 (coe d_regs_422 (coe v2))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v5 = d_halted_428 (coe v2) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                   else (let v6 = d_scratch_136 (coe d_regs_422 (coe v2)) in
                         coe
                           (let v7
                                  = coe
                                      du_exec'45'loop'45'run_3140 (coe v0) (coe v4)
                                      (coe
                                         du_loop'45'reanchor'45'loc_3128 (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe v0 v2 v3)))
                                      (coe
                                         du_loop'45'reanchor'45'alloc_3134 (coe v3)
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
d_lit'45'value_3200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 -> AgdaAny -> AgdaAny
d_lit'45'value_3200 v0 ~v1 v2 v3 = du_lit'45'value_3200 v0 v2 v3
du_lit'45'value_3200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_56 -> AgdaAny -> AgdaAny
du_lit'45'value_3200 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_fits'45'int_58
        -> coe
             MAlonzo.Code.Once.Word.d_fromℤ_20
             (coe
                mulInt (coe (8 :: Integer))
                (coe
                   MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'word_102 (coe v0)))
             (coe v2)
      MAlonzo.Code.Once.Type.C_fits'45'float_60
        -> coe
             MAlonzo.Code.Once.Float.Decimal.d_round_174
             (coe
                MAlonzo.Code.Once.CCC.FrameSemantics.d_float'45'format_118
                (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract
d_exec'45'abstract_3206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2246 ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_3206 v0 v1 v2 v3
  = case coe v1 of
      C_mov'45'to'45'output_2248
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Input1_56)))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      C_mov'45'to'45'input_2250
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Input1_56)
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Output_58)))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      C_load'45'indirect_2252
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'via'45'resolved_1482 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1378
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'indirect'45'suc_2254
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'load'45'suc'45'via'45'resolved_1520 (coe C_Output_58)
                (coe
                   du_sv'45'as'45'loc_1378
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Input1_56)))
                v2)
             (coe v3)
      C_load'45'from'45'slot_2256 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2614
             (coe
                du_readLoc_662 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_592 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_store'45'at'45'slot_2258 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_828 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_592 (coe v3)) (coe v4))
                (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_store'45'indirect_2260
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'via'45'resolved_1494 v0
                (coe
                   du_sv'45'as'45'loc_1378
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_store'45'indirect'45'suc_2262
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_exec'45'store'45'suc'45'via'45'resolved_1532 v0
                (coe
                   du_sv'45'as'45'loc_1378
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Input1_56)))
                (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Output_58))
                v2)
             (coe v3)
      C_lea'45'slot_2264 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_592 (coe v3)) (coe v4))))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      C_restore'45'input_2266 v4
        -> coe
             du_exec'45'restore'45'input'45'with'45'value_2626
             (coe
                du_readLoc_662 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_592 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_instr'45'alloc'45'stack_2268 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'dealloc'45'stack_2270 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'reclaim'45'to_2272 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'push'45'frame_2274 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'pop'45'frame_2276
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'call'45'closure_2278
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'init_2280 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_worklist'45'push_2282 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                d_writeLoc_828 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_592 (coe v3)) (coe v4))
                (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Output_58)))
             (coe v3)
      C_worklist'45'pop_2284 v4
        -> coe
             du_exec'45'load'45'from'45'slot'45'with'45'value_2614
             (coe
                du_readLoc_662 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                   (coe d_current'45'frame_592 (coe v3)) (coe v4)))
             (coe v2) (coe v3)
      C_worklist'45'check_2286 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'sigop_2292 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (d_exec'45'sigop'45'output_3088
                      (coe v0) (coe v4) (coe v5) (coe v6) (coe v2)))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe du_exec'45'sigop'45'halts_3104 (coe v6))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe d_ev'45'log_430 (coe v2))
                   (coe du_sigop'45'events_3078 (coe v4) (coe v6) (coe v2))))
             (coe v3)
      C_instr'45'load'45'const_2298 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Lit_76 (coe v4) (coe v5)
                      (coe du_lit'45'value_3200 (coe v0) (coe v5) (coe v6))))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      C_instr'45'load'45'code'45'addr_2300 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Code_78 (coe v4)))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      C_instr'45'save'45'closure'45'reg_2302
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr'45'load'45'tag'45'lit_2304 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (coe C_SV'45'Tag_72 (coe v4)))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe v3)
      C_instr'45'case'45'on'45'tag_2306 v4 v5
        -> coe
             d_exec'45'case'45'dispatch_3212 (coe v0)
             (coe du_case'45'tag'45'at_3112 (coe v2)) (coe v4) (coe v5) (coe v2)
             (coe v3)
      C_instr'45'alloc'45'heap_2308 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432
                (coe
                   du_writeReg_156 (d_regs_422 (coe v2)) (coe C_Output_58)
                   (coe
                      C_SV'45'Ptr_70
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                               (coe d_next'45'heap'45'ref_600 (coe v3)))))))
                (coe d_stackMem_424 (coe v2)) (coe d_heapMem_426 (coe v2))
                (coe d_halted_428 (coe v2)) (coe d_ev'45'log_430 (coe v2)))
             (coe
                C_mkAllocState_604 (coe d_current'45'frame_592 (coe v3))
                (coe d_saved'45'frames_594 (coe v3))
                (coe d_frame'45'slots_596 (coe v3))
                (coe d_next'45'slot_598 (coe v3))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Allocator.AbstractInstance.du_alloc'45'impl_52
                         (coe d_next'45'heap'45'ref_600 (coe v3)))))
                (coe
                   d_size'45'with_488 (coe v4)
                   (coe d_next'45'heap'45'ref_600 (coe v3))
                   (coe d_block'45'size_602 (coe v3))))
      C_instr'45'loop_2310 v4
        -> coe
             d_exec'45'loop_3210 (coe v0) (coe du_loop'45'fuel_3110) (coe v4)
             (coe v2) (coe v3)
      C_instr'45'reg'45'op_2312 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_exec'45'reg'45'op_454 (coe v4) (coe v2)) (coe v3)
      C_instr'45'ctrl_2314 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_lea'45'indexed_2316 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_exec'45'lea'45'indexed'45'via_1508
                (coe
                   du_slot'45'base_1504
                   (coe
                      du_readLoc_662 (coe v2)
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16
                         (coe d_current'45'frame_592 (coe v3)) (coe v4))))
                (d_sv'45'tag'45'val_402
                   (coe du_readReg_144 (coe d_regs_422 (coe v2)) (coe C_Scratch_60)))
                v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace
d_exec'45'trace_3208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2246] ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_3208 v0 v1 v2 v3
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      (:) v4 v5
        -> let v6 = d_halted_428 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'trace_3208 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe d_exec'45'abstract_3206 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_exec'45'abstract_3206 (coe v0) (coe v4) (coe v2) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-loop
d_exec'45'loop_3210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [T_AbstractInstr_2246] ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'loop_3210 v0 v1 v2 v3 v4
  = coe
      du_exec'45'loop'45'run_3140
      (coe d_exec'45'trace_3208 (coe v0) (coe v2)) (coe v1) (coe v3)
      (coe v4)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-case-dispatch
d_exec'45'case'45'dispatch_3212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe T_StoredValue_66 ->
  [T_AbstractInstr_2246] ->
  [T_AbstractInstr_2246] ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'case'45'dispatch_3212 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             C_SV'45'Ptr_70 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_432 (coe d_regs_422 (coe v4))
                       (coe d_stackMem_424 (coe v4)) (coe d_heapMem_426 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe d_ev'45'log_430 (coe v4)))
                    (coe v5)
             C_SV'45'Tag_72 v7
               -> case coe v7 of
                    0 -> coe d_exec'45'trace_3208 (coe v0) (coe v2) (coe v4) (coe v5)
                    _ -> coe d_exec'45'trace_3208 (coe v0) (coe v3) (coe v4) (coe v5)
             C_SV'45'Lit_76 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_432 (coe d_regs_422 (coe v4))
                       (coe d_stackMem_424 (coe v4)) (coe d_heapMem_426 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe d_ev'45'log_430 (coe v4)))
                    (coe v5)
             C_SV'45'Code_78 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mkLocState_432 (coe d_regs_422 (coe v4))
                       (coe d_stackMem_424 (coe v4)) (coe d_heapMem_426 (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe d_ev'45'log_430 (coe v4)))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mkLocState_432 (coe d_regs_422 (coe v4))
                (coe d_stackMem_424 (coe v4)) (coe d_heapMem_426 (coe v4))
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe d_ev'45'log_430 (coe v4)))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-cons
d_exec'45'trace'45'cons_3494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2246 ->
  [T_AbstractInstr_2246] ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'cons_3494 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-single
d_exec'45'trace'45'single_3540 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2246 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'single_3540 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.AllI
d_AllI_3574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_AbstractInstr_2246 -> ()) -> [T_AbstractInstr_2246] -> ()
d_AllI_3574 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-trace-alloc-invariant
d_exec'45'trace'45'alloc'45'invariant_3602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_500 -> AgdaAny) ->
  (T_AbstractInstr_2246 -> ()) ->
  (T_AbstractInstr_2246 ->
   T_LocState_408 ->
   T_AllocState_500 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2246] ->
  AgdaAny ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'alloc'45'invariant_3602 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-abstract-case-invariant
d_exec'45'abstract'45'case'45'invariant_3692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_AllocState_500 -> AgdaAny) ->
  (T_AbstractInstr_2246 -> ()) ->
  (T_AbstractInstr_2246 ->
   T_LocState_408 ->
   T_AllocState_500 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [T_AbstractInstr_2246] ->
  [T_AbstractInstr_2246] ->
  AgdaAny ->
  AgdaAny ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'abstract'45'case'45'invariant_3692 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.getTag
d_getTag_3824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_LocState_408 -> T_AllocState_500 -> Integer -> Maybe Integer
d_getTag_3824 ~v0 v1 v2 v3 = du_getTag_3824 v1 v2 v3
du_getTag_3824 ::
  T_LocState_408 -> T_AllocState_500 -> Integer -> Maybe Integer
du_getTag_3824 v0 v1 v2
  = let v3
          = coe d_stackMem_424 v0 (d_current'45'frame_592 (coe v1)) v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace
d_exec'45'tree'45'trace_3848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2434 ->
  T_LocState_408 ->
  T_AllocState_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'tree'45'trace_3848 v0 v1 v2 v3
  = case coe v1 of
      C_ε_2436
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      C_instr_2438 v4
        -> let v5 = d_halted_428 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'abstract_3206 (coe v0) (coe v4) (coe v2) (coe v3))
      C__'9656'__2440 v4 v5
        -> let v6 = d_halted_428 (coe v2) in
           coe
             (if coe v6
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3848 (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_exec'45'tree'45'trace_3848 (coe v0) (coe v4) (coe v2) (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_exec'45'tree'45'trace_3848 (coe v0) (coe v4) (coe v2) (coe v3))))
      C_branch_2442 v4 v5 v6
        -> let v7 = d_halted_428 (coe v2) in
           coe
             (if coe v7
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else (let v8
                            = coe d_stackMem_424 v2 (d_current'45'frame_592 (coe v3)) v4 in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                             -> let v10 = 0 :: Integer in
                                coe
                                  (case coe v10 of
                                     0 -> coe
                                            d_exec'45'tree'45'trace_3848 (coe v0) (coe v5) (coe v2)
                                            (coe v3)
                                     _ -> coe
                                            d_exec'45'tree'45'trace_3848 (coe v0) (coe v6) (coe v2)
                                            (coe v3))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                    -> case coe v9 of
                                         0 -> coe
                                                d_exec'45'tree'45'trace_3848 (coe v0) (coe v5)
                                                (coe v2) (coe v3)
                                         _ -> coe
                                                d_exec'45'tree'45'trace_3848 (coe v0) (coe v6)
                                                (coe v2) (coe v3)
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    -> coe
                                         d_exec'45'tree'45'trace_3848 (coe v0) (coe v5) (coe v2)
                                         (coe v3)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      C_call'45'sub_2444 v4
        -> let v5 = d_halted_428 (coe v2) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
                else coe
                       d_exec'45'tree'45'trace_3848 (coe v0) (coe v4) (coe v2) (coe v3))
      C_flat_2446 v4
        -> coe d_exec'45'trace_3208 (coe v0) (coe v4) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-ε
d_exec'45'tree'45'trace'45'ε_4008 ::
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'ε_4008 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-seq
d_exec'45'tree'45'trace'45'seq_4026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2434 ->
  T_TreeTrace_2434 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'seq_4026 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-instr
d_exec'45'tree'45'trace'45'instr_4072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AbstractInstr_2246 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'instr_4072 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-call-sub
d_exec'45'tree'45'trace'45'call'45'sub_4112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2434 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'call'45'sub_4112 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-trace-flat
d_exec'45'tree'45'trace'45'flat_4152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [T_AbstractInstr_2246] ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'tree'45'trace'45'flat_4152 = erased
-- Once.CCC.Machine.SMCore.AbstractExec.exec-tree-flat-equiv-simple
d_exec'45'tree'45'flat'45'equiv'45'simple_4166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_TreeTrace_2434 ->
  T_LocState_408 ->
  T_AllocState_500 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exec'45'tree'45'flat'45'equiv'45'simple_4166 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_exec'45'tree'45'flat'45'equiv'45'simple_4166
du_exec'45'tree'45'flat'45'equiv'45'simple_4166 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_exec'45'tree'45'flat'45'equiv'45'simple_4166
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
