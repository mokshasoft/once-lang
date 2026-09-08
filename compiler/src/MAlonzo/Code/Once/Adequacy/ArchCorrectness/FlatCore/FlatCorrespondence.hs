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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.clos-reg
d_clos'45'reg_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_clos'45'reg_32 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_clos'45'reg_32 v5
du_clos'45'reg_32 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_clos'45'reg_32 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_clos'45'reg_38
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.count-reg
d_count'45'reg_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_count'45'reg_34 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_count'45'reg_34 v5
du_count'45'reg_34 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_count'45'reg_34 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_count'45'reg_48
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.heap-reg
d_heap'45'reg_36 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_heap'45'reg_36 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_heap'45'reg_36 v5
du_heap'45'reg_36 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_heap'45'reg_36 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_heap'45'reg_40
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.in1-reg
d_in1'45'reg_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_in1'45'reg_38 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_in1'45'reg_38 v5
du_in1'45'reg_38 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_in1'45'reg_38 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_44
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.out-reg
d_out'45'reg_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_out'45'reg_40 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_out'45'reg_40 v5
du_out'45'reg_40 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_out'45'reg_40 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_out'45'reg_42
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reg-of
d_reg'45'of_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  AgdaAny
d_reg'45'of_42 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_reg'45'of_42 v5
du_reg'45'of_42 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  AgdaAny
du_reg'45'of_42 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.d_reg'45'of_34
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.scratch-reg
d_scratch'45'reg_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_scratch'45'reg_44 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_scratch'45'reg_44 v5
du_scratch'45'reg_44 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_scratch'45'reg_44 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_46
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sp-reg
d_sp'45'reg_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_sp'45'reg_46 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_sp'45'reg_46 v5
du_sp'45'reg_46 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  AgdaAny
du_sp'45'reg_46 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slots
d_slots_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> Integer -> Integer
d_slots_48 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_slots_48 v1 v10
du_slots_48 :: Integer -> Integer -> Integer
du_slots_48 v0 v1 = coe mulInt (coe v1) (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slot-to-disp
d_slot'45'to'45'disp_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> Integer -> Integer
d_slot'45'to'45'disp_52 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_slot'45'to'45'disp_52 v1 v10
du_slot'45'to'45'disp_52 :: Integer -> Integer -> Integer
du_slot'45'to'45'disp_52 v0 v1 = coe mulInt (coe v1) (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.nz⇒pos
d_nz'8658'pos_58 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nz'8658'pos_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_nz'8658'pos_58
du_nz'8658'pos_58 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nz'8658'pos_58
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slot-size>0
d_slot'45'size'62'0_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'size'62'0_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_slot'45'size'62'0_60
du_slot'45'size'62'0_60 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'size'62'0_60 = coe du_nz'8658'pos_58
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Word
d_Word_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) -> (AgdaAny -> Bool) -> ()
d_Word_62 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Memory
d_Memory_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) -> (AgdaAny -> Bool) -> ()
d_Memory_64 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.readMem
d_readMem_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_readMem_66 v10 v11
du_readMem_66 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
du_readMem_66 v0 v1 = coe v0 v1
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.writeMem
d_writeMem_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
              v13
  = du_writeMem_72 v10 v11 v12 v13
du_writeMem_72 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
du_writeMem_72 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.readLoc
d_readLoc_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_readLoc_84
du_readLoc_84 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_84
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeHeapMem
d_writeHeapMem_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_writeHeapMem_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeHeapMem_86
du_writeHeapMem_86 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_writeHeapMem_86
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_782
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeLoc
d_writeLoc_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLoc_88 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeLoc_88 v0
du_writeLoc_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLoc_88 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_810 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeLocToHeap
d_writeLocToHeap_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToHeap_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeLocToHeap_94
du_writeLocToHeap_94 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToHeap_94
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_802
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeLocToStack
d_writeLocToStack_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_writeLocToStack_96 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeLocToStack_96 v0
du_writeLocToStack_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_writeLocToStack_96 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_792 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'suc'45'via'45'resolved_100 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 ~v9
  = du_exec'45'load'45'suc'45'via'45'resolved_100
du_exec'45'load'45'suc'45'via'45'resolved_100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'suc'45'via'45'resolved_100
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1502
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'load'45'via'45'resolved_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9
  = du_exec'45'load'45'via'45'resolved_102
du_exec'45'load'45'via'45'resolved_102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'load'45'via'45'resolved_102
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1464
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'suc'45'via'45'resolved_106 v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 ~v9
  = du_exec'45'store'45'suc'45'via'45'resolved_106 v0
du_exec'45'store'45'suc'45'via'45'resolved_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'store'45'suc'45'via'45'resolved_106 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_exec'45'store'45'via'45'resolved_108 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9
  = du_exec'45'store'45'via'45'resolved_108 v0
du_exec'45'store'45'via'45'resolved_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_exec'45'store'45'via'45'resolved_108 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1476
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState
d_FlatState_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.do-ret
d_do'45'ret_154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_do'45'ret_154
du_do'45'ret_154 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_154
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_968
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.do-thunk
d_do'45'thunk_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_168 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_do'45'thunk_168 v0
du_do'45'thunk_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_168 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_1102 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.enter-call
d_enter'45'call_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'call_170 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_enter'45'call_170 v0
du_enter'45'call_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_enter'45'call_170 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_788 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.flat-exec-instr
d_flat'45'exec'45'instr_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_234 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_flat'45'exec'45'instr_234 v0
du_flat'45'exec'45'instr_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_234 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1330
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.leave-frame
d_leave'45'frame_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_leave'45'frame_298
du_leave'45'frame_298 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame_298
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_804
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.leave-frame-aux
d_leave'45'frame'45'aux_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame'45'aux_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_leave'45'frame'45'aux_300
du_leave'45'frame'45'aux_300 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame'45'aux_300
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_792
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sv-is-zero
d_sv'45'is'45'zero_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_sv'45'is'45'zero_364
du_sv'45'is'45'zero_364 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_364
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.falloc
d_falloc_382 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_382 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.fclosure
d_fclosure_384 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_384 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.flink
d_flink_386 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_386 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.floc
d_floc_388 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_388 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.fpc
d_fpc_390 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_390 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.fret
d_fret_392 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_392 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.shift-frame
d_shift'45'frame_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_404 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_shift'45'frame_404 v0
du_shift'45'frame_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
du_shift'45'frame_404 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sv-below
d_sv'45'below_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_sv'45'below_408 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.svm-below
d_svm'45'below_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> ()
d_svm'45'below_410 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-abstract
d_exec'45'abstract_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_414 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_exec'45'abstract_414 v0
du_exec'45'abstract_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_414 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2864
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.lit-value
d_lit'45'value_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 -> AgdaAny -> AgdaAny
d_lit'45'value_420 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_lit'45'value_420 v0
du_lit'45'value_420 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_192 -> AgdaAny -> AgdaAny
du_lit'45'value_420 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_lit'45'value_2858 (coe v0)
      v2 v3
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Frame
d_Frame_424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) -> (AgdaAny -> Bool) -> ()
d_Frame_424 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.frame-base
d_frame'45'base_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny -> Integer
d_frame'45'base_426 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_frame'45'base_426 v0
du_frame'45'base_426 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
du_frame'45'base_426 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.slot-addr
d_slot'45'addr_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny -> Integer -> Integer
d_slot'45'addr_432 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_slot'45'addr_432 v0
du_slot'45'addr_432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_slot'45'addr_432 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView
d_HeapView_436 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_HeapView_436
  = C_mkHV_490 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                Integer)
               Integer (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer)
               (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
               Integer MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.haddr
d_haddr_464 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_464 v0
  = case coe v0 of
      C_mkHV_490 v1 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.HDom
d_HDom_466 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_466 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.hfront
d_hfront_468 :: T_HeapView_436 -> Integer
d_hfront_468 v0
  = case coe v0 of
      C_mkHV_490 v1 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.caddr
d_caddr_470 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_470 v0
  = case coe v0 of
      C_mkHV_490 v1 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.haddr-suc
d_haddr'45'suc_474 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_474 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.haddr-inj
d_haddr'45'inj_480 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_480 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.dom-below
d_dom'45'below_484 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_484 v0
  = case coe v0 of
      C_mkHV_490 v1 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.lo
d_lo_486 :: T_HeapView_436 -> Integer
d_lo_486 v0
  = case coe v0 of
      C_mkHV_490 v1 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.front-lo
d_front'45'lo_488 ::
  T_HeapView_436 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_488 v0
  = case coe v0 of
      C_mkHV_490 v1 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.lit-word
d_lit'45'word_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> Integer -> Integer
d_lit'45'word_492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_lit'45'word_492 v10
du_lit'45'word_492 :: Integer -> Integer
du_lit'45'word_492 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.AddrMap
d_AddrMap_496 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_AddrMap_496
  = C_mkAddrMap_506 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                     Integer)
                    (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.AddrMap.hmap
d_hmap_502 ::
  T_AddrMap_496 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_502 v0
  = case coe v0 of
      C_mkAddrMap_506 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.AddrMap.cmap
d_cmap_504 ::
  T_AddrMap_496 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_504 v0
  = case coe v0 of
      C_mkAddrMap_506 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-sv-at
d_enc'45'sv'45'at_508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv'45'at_508 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      v11
  = du_enc'45'sv'45'at_508 v0 v10 v11
du_enc'45'sv'45'at_508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_496 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv'45'at_508 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
               -> coe
                    MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_92 v0 v4 v5
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
               -> coe d_hmap_502 v1 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v3 -> coe v3
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v3 v4 v5
        -> coe seq (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v3
        -> coe d_cmap_504 v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-maybe-at
d_enc'45'maybe'45'at_536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe'45'at_536 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                         v11
  = du_enc'45'maybe'45'at_536 v0 v10 v11
du_enc'45'maybe'45'at_536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_496 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe'45'at_536 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_enc'45'sv'45'at_508 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.amap
d_amap_544 :: T_HeapView_436 -> T_AddrMap_496
d_amap_544 v0
  = coe
      C_mkAddrMap_506 (coe d_haddr_464 (coe v0))
      (coe d_caddr_470 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-sv
d_enc'45'sv_548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv_548 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_enc'45'sv_548 v0 v10
du_enc'45'sv_548 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv_548 v0 v1
  = coe
      du_enc'45'sv'45'at_508 (coe v0)
      (coe
         C_mkAddrMap_506 (coe d_haddr_464 (coe v1))
         (coe d_caddr_470 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-maybe
d_enc'45'maybe_552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe_552 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_enc'45'maybe_552 v0 v10
du_enc'45'maybe_552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_436 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe_552 v0 v1
  = coe
      du_enc'45'maybe'45'at_536 (coe v0)
      (coe
         C_mkAddrMap_506 (coe d_haddr_464 (coe v1))
         (coe d_caddr_470 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.frames-of
d_frames'45'of_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_frames'45'of_556 v10
du_frames'45'of_556 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_556 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Window
d_Window_560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny -> Integer -> ()
d_Window_560 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.StackWindows
d_StackWindows_576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_576 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.GapNext
d_GapNext_600 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_GapNext_600 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.RetAddrs
d_RetAddrs_610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer] -> ()
d_RetAddrs_610 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-unlink
d_ret'45'unlink_684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_ret'45'unlink_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                    ~v11 ~v12 v13 ~v14 ~v15 ~v16 v17 v18 v19
  = du_ret'45'unlink_684 v10 v13 v17 v18 v19
du_ret'45'unlink_684 ::
  (Integer -> Integer) ->
  Maybe Integer ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_ret'45'unlink_684 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v5 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3 (coe v0 v5) v8)
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe seq (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-relink
d_ret'45'relink_770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_ret'45'relink_770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                    ~v11 ~v12 v13 ~v14 ~v15 ~v16 v17 v18 v19
  = du_ret'45'relink_770 v10 v13 v17 v18 v19
du_ret'45'relink_770 ::
  (Integer -> Integer) ->
  Maybe Integer ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_ret'45'relink_770 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v5 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3 (coe v0 v5) v8)
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe seq (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-relk
d_ret'45'relk_856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ret'45'relk_856 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                  ~v12 ~v13 v14 v15 v16 v17 v18
  = du_ret'45'relk_856 v0 v1 v10 v14 v15 v16 v17 v18
du_ret'45'relk_856 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ret'45'relk_856 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v8 v9
        -> case coe v4 of
             (:) v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                      -> case coe v10 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> case coe v16 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   v6
                                                   (addInt
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                         v0 v13)
                                                      (coe du_slots_48 (coe v1) (coe v14)))
                                                   (coe v2 v8) v15)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v17)
                                                   (coe
                                                      du_ret'45'relk_856 (coe v0) (coe v1) (coe v2)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                      (coe v11) (coe v9) (coe v6) (coe v18)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           seq (coe v10)
                           (case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                -> case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                               (coe
                                                  du_ret'45'relk_856 (coe v0) (coe v1) (coe v2)
                                                  (coe v3) (coe v11) (coe v9) (coe v6) (coe v15)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-head
d_ret'45'head_962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_ret'45'head_962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21
  = du_ret'45'head_962 v13 v19 v21
du_ret'45'head_962 ::
  Maybe Integer -> [Integer] -> AgdaAny -> AgdaAny
du_ret'45'head_962 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> coe
             seq (coe v0)
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe seq (coe v6) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr
d_FlatCorr_1056 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_FlatCorr_1056
  = C_constructor_1148 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny)
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.in1-eq
d_in1'45'eq_1106 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_1106 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.out-eq
d_out'45'eq_1108 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_1108 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.scratch-eq
d_scratch'45'eq_1110 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_1110 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.count-eq
d_count'45'eq_1112 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_1112 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.clos-eq
d_clos'45'eq_1114 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_1114 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.halt-eq
d_halt'45'eq_1116 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_1116 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.sp-eq
d_sp'45'eq_1118 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_1118 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.frontier-eq
d_frontier'45'eq_1120 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_1120 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.dom-fresh
d_dom'45'fresh_1124 ::
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_1124 v0
  = case coe v0 of
      C_constructor_1148 v9 v10 v11 v13 v15 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.dom-written
d_dom'45'written_1130 ::
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_1130 v0
  = case coe v0 of
      C_constructor_1148 v9 v10 v11 v13 v15 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.dom-sized
d_dom'45'sized_1134 ::
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_1134 v0
  = case coe v0 of
      C_constructor_1148 v9 v10 v11 v13 v15 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.heap-eq
d_heap'45'eq_1138 ::
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_1138 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.lo-le
d_lo'45'le_1140 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_1140 v0
  = case coe v0 of
      C_constructor_1148 v9 v10 v11 v13 v15 -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.untouched
d_untouched_1144 ::
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_1144 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.stack-eq
d_stack'45'eq_1146 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_1146 v0
  = case coe v0 of
      C_constructor_1148 v9 v10 v11 v13 v15 -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole
d_SetsRole_1158 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_SetsRole_1158 = C_constructor_1188
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.at-role
d_at'45'role_1178 ::
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_1178 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.off-role
d_off'45'role_1182 ::
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_1182 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.keeps-mem
d_keeps'45'mem_1184 ::
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_1184 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.keeps-halt
d_keeps'45'halt_1186 ::
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_1186 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-in1
d_keep'45'in1_1210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in1_1210 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-out
d_keep'45'out_1214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'out_1214 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-scratch
d_keep'45'scratch_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'scratch_1218 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-count
d_keep'45'count_1222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'count_1222 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-clos
d_keep'45'clos_1226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'clos_1226 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-sp
d_keep'45'sp_1230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'sp_1230 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-heap-reg
d_keep'45'heap'45'reg_1234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap'45'reg_1234 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-halt
d_keep'45'halt_1238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'halt_1238 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-heap
d_keep'45'heap_1242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap_1242 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-lo-le
d_keep'45'lo'45'le_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_keep'45'lo'45'le_1250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_keep'45'lo'45'le_1250 v16
du_keep'45'lo'45'le_1250 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_keep'45'lo'45'le_1250 v0 = coe d_lo'45'le_1140 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-untouched
d_keep'45'untouched_1258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'untouched_1258 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-stack
d_keep'45'stack_1268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_keep'45'stack_1268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17
  = du_keep'45'stack_1268 v16
du_keep'45'stack_1268 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_keep'45'stack_1268 v0 = coe d_stack'45'eq_1146 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem
d_SetsMem_1280 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_SetsMem_1280 = C_constructor_1314
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.at-addr
d_at'45'addr_1302 ::
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_1302 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.off-addr
d_off'45'addr_1306 ::
  T_SetsMem_1280 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_1306 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.mem-regs
d_mem'45'regs_1310 ::
  T_SetsMem_1280 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_1310 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.mem-halt
d_mem'45'halt_1312 ::
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_1312 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-in1
d_mkeep'45'in1_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in1_1336 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-out
d_mkeep'45'out_1338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'out_1338 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-scratch
d_mkeep'45'scratch_1340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'scratch_1340 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-count
d_mkeep'45'count_1342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'count_1342 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-clos
d_mkeep'45'clos_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'clos_1344 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-sp
d_mkeep'45'sp_1346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'sp_1346 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-heap-reg
d_mkeep'45'heap'45'reg_1348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'heap'45'reg_1348 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-halt
d_mkeep'45'halt_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'halt_1350 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-lo-le
d_mkeep'45'lo'45'le_1352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mkeep'45'lo'45'le_1352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17
  = du_mkeep'45'lo'45'le_1352 v16
du_mkeep'45'lo'45'le_1352 ::
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mkeep'45'lo'45'le_1352 v0 = coe d_lo'45'le_1140 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem
d_SetsRoleMem_1368 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                   a14 a15
  = ()
data T_SetsRoleMem_1368 = C_constructor_1410
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-at-role
d_rm'45'at'45'role_1396 ::
  T_SetsRoleMem_1368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_1396 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-off-role
d_rm'45'off'45'role_1400 ::
  T_SetsRoleMem_1368 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_1400 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-at-addr
d_rm'45'at'45'addr_1402 ::
  T_SetsRoleMem_1368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_1402 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-off-addr
d_rm'45'off'45'addr_1406 ::
  T_SetsRoleMem_1368 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_1406 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-halt
d_rm'45'halt_1408 ::
  T_SetsRoleMem_1368 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_1408 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles
d_Sets2Roles_1424 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                  a15
  = ()
data T_Sets2Roles_1424 = C_constructor_1462
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.at-role₁
d_at'45'role'8321'_1450 ::
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_1450 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.at-role₂
d_at'45'role'8322'_1452 ::
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_1452 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.off-roles
d_off'45'roles_1456 ::
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_1456 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.keeps-mem₂
d_keeps'45'mem'8322'_1458 ::
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_1458 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.keeps-halt₂
d_keeps'45'halt'8322'_1460 ::
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_1460 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.win-at
d_win'45'at_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_1480 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.win-off
d_win'45'off_1526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_1526 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.stack-eq-win
d_stack'45'eq'45'win_1562 ::
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_1562 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.stack-eq-cur
d_stack'45'eq'45'cur_1576 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_1576 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sep
d_sep_1592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_1592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
           v13
  = du_sep_1592 v10 v13
du_sep_1592 ::
  T_HeapView_436 ->
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_1592 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_front'45'lo_488 (coe v0)) (coe d_lo'45'le_1140 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.descend-view
d_descend'45'view_1602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_436
d_descend'45'view_1602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                       v11 ~v12 v13
  = du_descend'45'view_1602 v10 v11 v13
du_descend'45'view_1602 ::
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_436
du_descend'45'view_1602 v0 v1 v2
  = coe
      C_mkHV_490 (d_haddr_464 (coe v0)) (d_hfront_468 (coe v0))
      (d_caddr_470 (coe v0)) (d_dom'45'below_484 (coe v0)) v1 v2
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-descend
d_untouched'45'descend_1626 ::
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_1626 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-mov-to-output
d_sim'45'mov'45'to'45'output_1650 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'mov'45'to'45'output_1650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'mov'45'to'45'output_1650 v14
du_sim'45'mov'45'to'45'output_1650 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'mov'45'to'45'output_1650 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-mov-to-input
d_sim'45'mov'45'to'45'input_1672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'mov'45'to'45'input_1672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'mov'45'to'45'input_1672 v14
du_sim'45'mov'45'to'45'input_1672 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'mov'45'to'45'input_1672 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_1696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'tag'45'lit_1696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'load'45'tag'45'lit_1696 v15
du_sim'45'load'45'tag'45'lit_1696 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'tag'45'lit_1696 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_1720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'reg'45'scratch'45'one_1720 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'scratch'45'one_1720 v14
du_sim'45'reg'45'scratch'45'one_1720 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'reg'45'scratch'45'one_1720 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_1742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'reg'45'scratch'45'zero_1742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'scratch'45'zero_1742 v14
du_sim'45'reg'45'scratch'45'zero_1742 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'reg'45'scratch'45'zero_1742 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_1764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'reg'45'count'45'zero_1764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'count'45'zero_1764 v14
du_sim'45'reg'45'count'45'zero_1764 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'reg'45'count'45'zero_1764 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_1786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'reg'45'scratch'45'load'45'count_1786 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'scratch'45'load'45'count_1786 v14
du_sim'45'reg'45'scratch'45'load'45'count_1786 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'reg'45'scratch'45'load'45'count_1786 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sv-tag-zero
d_sv'45'tag'45'zero_1802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_1802 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-zero
d_enc'45'zero_1810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_1810 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_1826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'indirect'45'suc_1826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_sim'45'load'45'indirect'45'suc_1826 v16
du_sim'45'load'45'indirect'45'suc_1826 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'indirect'45'suc_1826 v0
  = coe du_corr'45'clean_1864 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_1852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1852 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_1852 v12 v13
du_cleanFlat_1852 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1852 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_1854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1854 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1860 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_1864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_corr'45'clean_1864 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_1864 v16
du_corr'45'clean_1864 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_1864 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect
d_sim'45'load'45'indirect_1880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'indirect_1880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_sim'45'load'45'indirect_1880 v16
du_sim'45'load'45'indirect_1880 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'indirect_1880 v0
  = coe du_corr'45'clean_1918 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_1906 v12 v13
du_cleanFlat_1906 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1906 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_1908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1908 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_1914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1914 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_1918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_corr'45'clean_1918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_1918 v16
du_corr'45'clean_1918 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_1918 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-from-slot
d_sim'45'load'45'from'45'slot_1934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'from'45'slot_1934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_sim'45'load'45'from'45'slot_1934 v16
du_sim'45'load'45'from'45'slot_1934 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'from'45'slot_1934 v0
  = coe du_corr'45'clean_1968 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.ex-eq
d_ex'45'eq_1958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_1958 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_1962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1962 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cleanFlat_1962 v12 v13
du_cleanFlat_1962 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1962 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_1964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1964 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_1968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_corr'45'clean_1968 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_corr'45'clean_1968 v16
du_corr'45'clean_1968 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_1968 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.≡ᵇ-refl
d_'8801''7495''45'refl_1974 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_1974 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_1982 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_1982 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-write
d_untouched'45'write_2008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  T_SetsMem_1280 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_2008 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-heap-store
d_untouched'45'heap'45'store_2036 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_2036 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-stack-store
d_untouched'45'stack'45'store_2078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_2078 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-heap-eq
d_store'45'heap'45'eq_2118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_SetsMem_1280 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_2118 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-dom-written
d_store'45'dom'45'written_2210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_store'45'dom'45'written_2210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11 ~v12 ~v13 v14 v15 v16 v17 v18
  = du_store'45'dom'45'written_2210 v11 v14 v15 v16 v17 v18
du_store'45'dom'45'written_2210 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_2210 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Memory.HeapAddress.du_'8799'HL'45'aux_62
              (let v6
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                         erased
                         (\ v6 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                              (coe
                                 MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                 (coe
                                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                    (coe v0))))
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                            (coe
                               eqInt
                               (coe
                                  MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                     (coe v0)))
                               (coe
                                  MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                     (coe v3))))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                               (coe
                                  eqInt
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                     (coe
                                        MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48
                                        (coe v3)))))) in
               coe
                 (case coe v6 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                      -> if coe v7
                           then coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                           else coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe v7)
                                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                    _ -> MAlonzo.RTE.mazUnreachableError))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                 (coe
                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v0))
                 (coe
                    MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50
                    (coe v3))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe seq (coe v8) (coe v1)
                else coe seq (coe v8) (coe v2 v3 v4 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.read-write-hit
d_read'45'write'45'hit_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'hit_2272 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.read-write-miss
d_read'45'write'45'miss_2292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_2292 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-reanchor
d_windows'45'reanchor_2324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'reanchor_2324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19
  = du_windows'45'reanchor_2324 v18 v19
du_windows'45'reanchor_2324 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_2324 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             seq (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-lower
d_windows'45'lower_2354 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'lower_2354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17
  = du_windows'45'lower_2354 v15 v16 v17
du_windows'45'lower_2354 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'lower_2354 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> coe
             seq (coe v3)
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
                             (coe v5))
                          (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-forget
d_windows'45'forget_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'forget_2400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17
  = du_windows'45'forget_2400 v15 v16 v17
du_windows'45'forget_2400 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'forget_2400 v0 v1 v2
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        (\ v11 v12 v13 v14 ->
                                           coe v9 v11 v12 v13 (coe v1 v5 v11 v13 v14)))
                                     (coe du_windows'45'forget_2400 (coe v4) erased (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-leave
d_windows'45'leave_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_2454 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                        ~v11 ~v12 v13 ~v14 v15
  = du_windows'45'leave_2454 v0 v13 v15
du_windows'45'leave_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_2454 v0 v1 v2
  = coe
      du_go_2474 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
         (coe v1))
      (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2474 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 v13
          ~v14 ~v15 v16 ~v17 v18
  = du_go_2474 v0 v13 v16 v18
du_go_2474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2474 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             seq (coe v4)
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                           (coe v6)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                    v0
                                                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
                                                       (coe v1))))
                                              (coe v10)))
                                        (coe v11))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-above
d_windows'45'above_2520 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'above_2520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 v19
  = du_windows'45'above_2520 v16 v19
du_windows'45'above_2520 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'above_2520 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v2 v3
        -> coe
             seq (coe v2)
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe du_windows'45'above_2520 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.up
d_up_2570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_up_2570 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_up_2570 v0 v16 v21
du_up_2570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_up_2570 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.window-store-above
d_window'45'store'45'above_2602 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_window'45'store'45'above_2602 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-store-gap
d_windows'45'store'45'gap_2644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'store'45'gap_2644 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17 ~v18 v19
  = du_windows'45'store'45'gap_2644 v0 v1 v15 v16 v17 v19
du_windows'45'store'45'gap_2644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'store'45'gap_2644 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      []
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v6 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe
                                        du_windows'45'lower_2354 (coe v4)
                                        (coe
                                           du_a'8804'next_2704 (coe v0) (coe v1) (coe v2) (coe v3))
                                        (coe
                                           du_windows'45'above_2520 (coe v4)
                                           (coe
                                              du_windows'45'reanchor_2324
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                    v0 v8))
                                              (coe v13)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a
d_a_2698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_a_2698 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_a_2698 v0 v1 v15 v16
du_a_2698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> AgdaAny -> Integer -> Integer
du_a_2698 v0 v1 v2 v3
  = coe
      addInt
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2)
      (coe du_slots_48 (coe v1) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a<next
d_a'60'next_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'60'next_2700 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_a'60'next_2700 v0 v1 v15 v16
du_a'60'next_2700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'60'next_2700 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
      (coe du_a_2698 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_slot'45'size'62'0_60)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a≤next
d_a'8804'next_2704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'8804'next_2704 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_a'8804'next_2704 v0 v1 v15 v16
du_a'8804'next_2704 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'8804'next_2704 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
      (coe du_a'60'next_2700 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-write-below
d_windows'45'write'45'below_2734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_2734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19
  = du_windows'45'write'45'below_2734 v17
du_windows'45'write'45'below_2734 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_2734 v0
  = coe du_windows'45'above_2520 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-heap-store
d_windows'45'heap'45'store_2782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_2782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_windows'45'heap'45'store_2782 v11 v17
du_windows'45'heap'45'store_2782 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_2782 v0 v1
  = coe
      du_windows'45'write'45'below_2734
      (coe
         du_frames'45'of_556
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
      (d_stack'45'eq_1146 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect
d_sim'45'store'45'indirect_2810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_sim'45'store'45'indirect_2810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_sim'45'store'45'indirect_2810 v11 v12 v15 v17
du_sim'45'store'45'indirect_2810 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> AgdaAny -> T_FlatCorr_1056
du_sim'45'store'45'indirect_2810 v0 v1 v2 v3
  = coe du_corr'45'clean_2848 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.v
d_v_2836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_v_2836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_v_2836 v12
du_v_2836 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_v_2836 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_2838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_2838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_2838 v11 v12
du_cleanFlat_2838 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_2838 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_802
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))
         (coe v0) (coe du_v_2836 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_2840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2840 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_2844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2844 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_2848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_corr'45'clean_2848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_corr'45'clean_2848 v11 v12 v15 v17
du_corr'45'clean_2848 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> AgdaAny -> T_FlatCorr_1056
du_corr'45'clean_2848 v0 v1 v2 v3
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v2))
      (coe
         du_store'45'dom'45'written_2210 (coe v0) (coe v3)
         (coe d_dom'45'written_1130 (coe v2)))
      (d_dom'45'sized_1134 (coe v2))
      (coe du_mkeep'45'lo'45'le_1352 (coe v2))
      (coe du_windows'45'heap'45'store_2782 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_2862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_sim'45'store'45'indirect'45'suc_2862 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_sim'45'store'45'indirect'45'suc_2862 v11 v12 v15 v17
du_sim'45'store'45'indirect'45'suc_2862 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> AgdaAny -> T_FlatCorr_1056
du_sim'45'store'45'indirect'45'suc_2862 v0 v1 v2 v3
  = coe du_corr'45'clean_2900 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.v
d_v_2888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_v_2888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_v_2888 v12
du_v_2888 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_v_2888 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_2890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_2890 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_2890 v11 v12
du_cleanFlat_2890 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_2890 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_802
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe du_v_2888 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_2892 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2892 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_2896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2896 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_2900 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_corr'45'clean_2900 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_corr'45'clean_2900 v11 v12 v15 v17
du_corr'45'clean_2900 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> AgdaAny -> T_FlatCorr_1056
du_corr'45'clean_2900 v0 v1 v2 v3
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v2))
      (coe
         du_store'45'dom'45'written_2210
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe v3) (coe d_dom'45'written_1130 (coe v2)))
      (d_dom'45'sized_1134 (coe v2))
      (coe du_mkeep'45'lo'45'le_1352 (coe v2))
      (coe du_windows'45'heap'45'store_2782 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-restore-input
d_sim'45'restore'45'input_2916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'restore'45'input_2916 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_sim'45'restore'45'input_2916 v16
du_sim'45'restore'45'input_2916 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'restore'45'input_2916 v0
  = coe du_corr'45'clean_2950 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.ex-eq
d_ex'45'eq_2940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_2940 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_2944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_2944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cleanFlat_2944 v12 v13
du_cleanFlat_2944 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_2944 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_2946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2946 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_2950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_corr'45'clean_2950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_corr'45'clean_2950 v16
du_corr'45'clean_2950 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_2950 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slot-addr-inj
d_slot'45'addr'45'inj_2960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_2960 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.atstack-slot-inj
d_atstack'45'slot'45'inj_2976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_2976 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.atstack-frame-inj
d_atstack'45'frame'45'inj_2988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_2988 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_3008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  T_SetsMem_1280 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_3008 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_3060 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_SetsMem_1280 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_3060 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.just-inj
d_just'45'inj_3100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_SetsMem_1280 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_3100 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_3102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  T_SetsMem_1280 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3102 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-slot-store
d_windows'45'slot'45'store_3136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_3136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 v22
  = du_windows'45'slot'45'store_3136 v19 v22
du_windows'45'slot'45'store_3136 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_3136 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe du_windows'45'above_2520 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.waddr
d_waddr_3172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer
d_waddr_3172 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_waddr_3172 v0 v1 v14 v16
du_waddr_3172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> AgdaAny -> Integer -> Integer
du_waddr_3172 v0 v1 v2 v3
  = coe
      addInt
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2)
      (coe du_slot'45'to'45'disp_52 (coe v1) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.w<fl
d_w'60'fl_3174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'fl_3174 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
  = du_w'60'fl_3174 v0 v1 v14 v15 v16 v21
du_w'60'fl_3174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'fl_3174 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
         (coe v1) (coe v4) (coe v3) (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base<
d_base'60'_3178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base'60'_3178 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25
                v26
  = du_base'60'_3178 v0 v1 v14 v15 v16 v21 v25 v26
du_base'60'_3178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_base'60'_3178 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2)
      (addInt
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v8 v9 -> v9) (\ v8 -> mulInt (coe v8) (coe v1)) (0 :: Integer)
            v3)
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2))
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v6)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
         (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2)
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
            (coe v1) (coe (0 :: Integer)) (coe v3)
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'691'_6712
               (0 :: Integer) v4 v3 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
               v5)))
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-at-slot
d_sim'45'store'45'at'45'slot_3208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_sim'45'store'45'at'45'slot_3208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18
  = du_sim'45'store'45'at'45'slot_3208 v12 v15
du_sim'45'store'45'at'45'slot_3208 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'store'45'at'45'slot_3208 v0 v1
  = coe du_corr'45'clean_3242 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base
d_base_3232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> Integer
d_base_3232 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_base_3232 v5 v7 v13
du_base_3232 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) -> AgdaAny -> Integer
du_base_3232 v0 v1 v2
  = coe
      v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Out
d_Out_3234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_Out_3234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_Out_3234 v12
du_Out_3234 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_Out_3234 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> AgdaAny
d_cf_3236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cf_3236 v12
du_cf_3236 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3236 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sm-base
d_sm'45'base_3238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_SetsMem_1280
d_sm'45'base_3238 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_3242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_corr'45'clean_3242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18
  = du_corr'45'clean_3242 v12 v15
du_corr'45'clean_3242 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_3242 v0 v1
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v1))
      (d_dom'45'written_1130 (coe v1)) (d_dom'45'sized_1134 (coe v1))
      (coe du_mkeep'45'lo'45'le_1352 (coe v1))
      (coe
         du_windows'45'slot'45'store_3136
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1146 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-alloc-stack
d_sim'45'alloc'45'stack_3262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'alloc'45'stack_3262 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10 v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_sim'45'alloc'45'stack_3262 v0 v1 v11 v12 v15 v20
du_sim'45'alloc'45'stack_3262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_1056
du_sim'45'alloc'45'stack_3262 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v4))
      (d_dom'45'written_1130 (coe v4)) (d_dom'45'sized_1134 (coe v4)) v5
      (coe
         du_windows'45's_3332 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> AgdaAny
d_cf_3294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_cf_3294 v12
du_cf_3294 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3294 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.newbase
d_newbase_3296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_3296 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.stk
d_stk_3306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stk_3306 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.tail-le
d_tail'45'le_3328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_3328 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                  v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_tail'45'le_3328 v0 v1 v11 v12
du_tail'45'le_3328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_3328 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 v0
               (coe du_cf_3294 (coe v3)) v2))
         (coe du_slots_48 (coe v1) (coe v2)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.windows-s
d_windows'45's_3332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45's_3332 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_windows'45's_3332 v0 v1 v11 v12 v15 v20
du_windows'45's_3332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45's_3332 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            du_windows'45'reanchor_2324
            (coe du_tail'45'le_3328 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe d_stack'45'eq_1146 (coe v4))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-thunk
d_sim'45'thunk_3364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'thunk_3364 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_sim'45'thunk_3364 v0 v1 v11 v12 v15 v19
du_sim'45'thunk_3364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_1056
du_sim'45'thunk_3364 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v4))
      (d_dom'45'written_1130 (coe v4)) (d_dom'45'sized_1134 (coe v4)) v5
      (coe
         du_windows'45's_3458 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> AgdaAny
d_cf_3394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_cf_3394 v12
du_cf_3394 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3394 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.nothing≢just
d_nothing'8802'just_3400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_3400 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.head-window
d_head'45'window_3406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_head'45'window_3406 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.newbase
d_newbase_3448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_3448 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.tail-le
d_tail'45'le_3454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_3454 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                  v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_tail'45'le_3454 v0 v1 v11 v12
du_tail'45'le_3454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_3454 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 v0
               (coe du_cf_3394 (coe v3)) v2))
         (coe du_slots_48 (coe v1) (coe v2)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.windows-s
d_windows'45's_3458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45's_3458 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_windows'45's_3458 v0 v1 v11 v12 v15 v19
du_windows'45's_3458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45's_3458 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            du_windows'45'forget_2400
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
            erased
            (coe
               du_windows'45'lower_2354
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
                  (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                  (coe du_tail'45'le_3454 (coe v0) (coe v1) (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
                        (coe du_cf_3394 (coe v3)))))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_stack'45'eq_1146 (coe v4)))))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-call-frame
d_sim'45'call'45'frame_3496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'call'45'frame_3496 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13 ~v14 v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_sim'45'call'45'frame_3496 v0 v1 v5 v7 v12 v13 v15 v19
du_sim'45'call'45'frame_3496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_1056
du_sim'45'call'45'frame_3496 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v6))
      (d_dom'45'written_1130 (coe v6)) (d_dom'45'sized_1134 (coe v6)) v7
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               du_windows'45'reanchor_2324
               (coe
                  du_tail'45'floor_3536 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5))
               (coe
                  du_windows'45'above_2520
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe du_cf_3526 (coe v4))
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580
                           (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v4))))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v4))))
                  (coe
                     du_windows'45'reanchor_2324
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
                           (coe du_cf_3526 (coe v4))))
                     (coe d_stack'45'eq_1146 (coe v6)))))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> AgdaAny
d_cf_3526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_cf_3526 v12
du_cf_3526 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3526 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.newbase
d_newbase_3528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_3528 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.tail-floor
d_tail'45'floor_3536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1158 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'floor_3536 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                     v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_tail'45'floor_3536 v0 v1 v5 v7 v12 v13
du_tail'45'floor_3536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'floor_3536 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
               (coe
                  MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_106 v0
                  (coe du_cf_3526 (coe v4)) (1 :: Integer)))
            (coe du_slots_48 (coe v1) (coe (0 :: Integer)))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
            (coe
               v3 v5
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                  (coe v2)))
            (coe v1))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               v3 v5
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                  (coe v2)))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-dealloc-stack
d_sim'45'dealloc'45'stack_3580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'dealloc'45'stack_3580 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9
                               ~v10 ~v11 v12 v13 ~v14 v15 ~v16 ~v17
  = du_sim'45'dealloc'45'stack_3580 v0 v5 v7 v12 v13 v15
du_sim'45'dealloc'45'stack_3580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'dealloc'45'stack_3580 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_1148 (\ v6 v7 -> coe d_dom'45'fresh_1124 v5 v6 v7)
      (d_dom'45'written_1130 (coe v5))
      (\ v6 v7 -> coe d_dom'45'sized_1134 v5 v6 v7)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_1140 (coe v5))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               v2 v4
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                  (coe v1)))))
      (coe
         du_windows'45'leave_2454 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
         (coe d_stack'45'eq_1146 (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-ret
d_sim'45'ret_3628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'ret_3628 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 v11 ~v12
                  ~v13 v14 v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_sim'45'ret_3628 v0 v1 v5 v7 v11 v14 v15 v17
du_sim'45'ret_3628 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'ret_3628 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1148 (\ v8 v9 -> coe d_dom'45'fresh_1124 v7 v8 v9)
      (d_dom'45'written_1130 (coe v7))
      (\ v8 v9 -> coe d_dom'45'sized_1134 v7 v8 v9)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_1140 (coe v7))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
               (coe
                  v3 v6
                  (coe
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                     (coe v2))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
               (coe
                  addInt (coe du_slots_48 (coe v1) (coe v4))
                  (coe
                     v3 v6
                     (coe
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
                        (coe v2)))))))
      (coe
         du_windows'45'leave_2454 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v5))
         (coe d_stack'45'eq_1146 (coe v7)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-const
d_sim'45'load'45'const_3682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'const_3682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'load'45'const_3682 v15
du_sim'45'load'45'const_3682 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'const_3682 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-const-float
d_sim'45'load'45'const'45'float_3708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'const'45'float_3708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'load'45'const'45'float_3708 v15
du_sim'45'load'45'const'45'float_3708 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'const'45'float_3708 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-code-addr
d_sim'45'load'45'code'45'addr_3736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'code'45'addr_3736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_sim'45'load'45'code'45'addr_3736 v16
du_sim'45'load'45'code'45'addr_3736 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'code'45'addr_3736 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_3764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'save'45'closure'45'reg_3764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'save'45'closure'45'reg_3764 v14
du_sim'45'save'45'closure'45'reg_3764 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'save'45'closure'45'reg_3764 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.inc-enc
d_inc'45'enc_3784 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_3784 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.dec-enc
d_dec'45'enc_3794 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_496 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_3794 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_3808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'reg'45'count'45'inc_3808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16 ~v17
  = du_sim'45'reg'45'count'45'inc_3808 v15
du_sim'45'reg'45'count'45'inc_3808 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'reg'45'count'45'inc_3808 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_3838 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'reg'45'scratch'45'dec_3838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16 ~v17
  = du_sim'45'reg'45'scratch'45'dec_3838 v15
du_sim'45'reg'45'scratch'45'dec_3838 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'reg'45'scratch'45'dec_3838 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-aux
d_ext'45'addr'45'aux_3864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_3864 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 v11 ~v12 v13
  = du_ext'45'addr'45'aux_3864 v1 v10 v11 v13
du_ext'45'addr'45'aux_3864 ::
  Integer ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_3864 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    addInt (coe d_hfront_468 (coe v1))
                    (coe
                       du_slot'45'to'45'disp_52 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v2)))
             else coe seq (coe v5) (coe d_haddr_464 v1 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr
d_ext'45'addr_3882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_3882 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   v12
  = du_ext'45'addr_3882 v1 v10 v11 v12
du_ext'45'addr_3882 ::
  Integer ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_3882 v0 v1 v2 v3
  = coe
      du_ext'45'addr'45'aux_3864 (coe v0) (coe v1) (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v3)))
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ExtDom
d_ExtDom_3898 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_ExtDom_3898
  = C_ext'45'old_3908 AgdaAny |
    C_ext'45'fresh_3910 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-old
d_ext'45'addr'45'old_3918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_3918 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_3934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3934 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-fresh
d_ext'45'addr'45'fresh_3944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_3944 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_3960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3960 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-base
d_ext'45'addr'45'base_3968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_3968 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.+-not-<
d_'43''45'not'45''60'_3978 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_3978 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-suc-aux
d_ext'45'suc'45'aux_3996 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_3996 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-suc
d_ext'45'suc_4022 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_4022 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.extend-view
d_extend'45'view_4040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_436
d_extend'45'view_4040 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      v11 v12 ~v13 v14
  = du_extend'45'view_4040 v1 v10 v11 v12 v14
du_extend'45'view_4040 ::
  Integer ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_436
du_extend'45'view_4040 v0 v1 v2 v3 v4
  = coe
      C_mkHV_490 (coe du_ext'45'addr_3882 (coe v0) (coe v1) (coe v2))
      (addInt
         (coe d_hfront_468 (coe v1)) (coe du_slots_48 (coe v0) (coe v3)))
      (d_caddr_470 (coe v1))
      (coe du_below_4058 (coe v0) (coe v1) (coe v3)) (d_lo_486 (coe v1))
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.below
d_below_4058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3898 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_4058 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12
             ~v13 ~v14 v15 v16
  = du_below_4058 v1 v10 v12 v15 v16
du_below_4058 ::
  Integer ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3898 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_below_4058 v0 v1 v2 v3 v4
  = case coe v4 of
      C_ext'45'old_3908 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
             (coe d_haddr_464 v1 v3) (d_hfront_468 (coe v1))
             (addInt
                (coe d_hfront_468 (coe v1)) (coe du_slots_48 (coe v0) (coe v2)))
             (coe d_dom'45'below_484 v1 v3 v5)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                (coe d_hfront_468 (coe v1)))
      C_ext'45'fresh_3910 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
             (coe d_hfront_468 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v3))
                (coe v2) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cross
d_cross_4078 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross_4078 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.inj
d_inj_4096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3898 ->
  T_ExtDom_3898 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj_4096 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._._.addr-eq
d_addr'45'eq_4146 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_4146 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._._.off-eq
d_off'45'eq_4148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'eq_4148 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-ext
d_enc'45'ext_4164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_4164 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-ext-maybe
d_enc'45'ext'45'maybe_4248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_4248 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-enc-ext
d_windows'45'enc'45'ext_4298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_windows'45'enc'45'ext_4298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_windows'45'enc'45'ext_4298 v18 v20
du_windows'45'enc'45'ext_4298 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_4298 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v2 v3
        -> coe
             seq (coe v2)
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe du_windows'45'enc'45'ext_4298 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-alloc-heap
d_sim'45'alloc'45'heap_4380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 -> T_FlatCorr_1056
d_sim'45'alloc'45'heap_4380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                            ~v24
  = du_sim'45'alloc'45'heap_4380 v12 v15
du_sim'45'alloc'45'heap_4380 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'alloc'45'heap_4380 v0 v1
  = coe
      C_constructor_1148 (coe du_df_4454 (coe v0) (coe v1))
      (\ v2 v3 v4 ->
         coe C_ext'45'old_3908 (coe d_dom'45'written_1130 v1 v2 v3 erased))
      (coe du_ds_4422 (coe v0) (coe v1)) (d_lo'45'le_1140 (coe v1))
      (coe
         du_windows'45'enc'45'ext_4298
         (coe
            du_frames'45'of_556
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1146 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.st
d_st_4416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 -> Integer
d_st_4416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_st_4416 v12
du_st_4416 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
du_st_4416 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_584
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.dfr
d_dfr_4418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dfr_4418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_dfr_4418 v15
du_dfr_4418 ::
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dfr_4418 v0 = coe d_dom'45'fresh_1124 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.ds
d_ds_4422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3898
d_ds_4422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 v26
  = du_ds_4422 v12 v15 v25 v26
du_ds_4422 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3898
du_ds_4422 v0 v1 v2 v3
  = coe
      du_go_4434 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe du_st_4416 (coe v0)))
      (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._._.go
d_go_4434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3898
d_go_4434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 ~v26
          v27 v28
  = du_go_4434 v15 v25 v27 v28
du_go_4434 ::
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3898
du_go_4434 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe C_ext'45'fresh_3910 v3)
             else coe
                    seq (coe v5)
                    (coe C_ext'45'old_3908 (coe d_dom'45'sized_1134 v0 v1 v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.hv'
d_hv''_4442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 -> T_HeapView_436
d_hv''_4442 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 v23 ~v24
  = du_hv''_4442 v1 v10 v11 v12 v23
du_hv''_4442 ::
  Integer ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_436
du_hv''_4442 v0 v1 v2 v3 v4
  = coe
      du_extend'45'view_4040 (coe v0) (coe v1) (coe du_st_4416 (coe v3))
      (coe v2) (coe v4)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.fresh-x86
d_fresh'45'x86_4446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'45'x86_4446 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.df
d_df_4454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3898 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_df_4454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 v25 v26
  = du_df_4454 v12 v15 v25 v26
du_df_4454 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3898 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_df_4454 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_3908 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3204
             (coe du_dfr_4418 v1 v2 v4)
      C_ext'45'fresh_3910 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe addInt (coe (1 :: Integer)) (coe du_st_4416 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.hp
d_hp_4464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_Sets2Roles_1424 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3898 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hp_4464 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-lea-slot
d_sim'45'lea'45'slot_4508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'lea'45'slot_4508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'lea'45'slot_4508 v15
du_sim'45'lea'45'slot_4508 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'lea'45'slot_4508 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_4528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny -> T_FlatCorr_1056 -> T_SetsRole_1158 -> AgdaAny
d_cf_4528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16
  = du_cf_4528 v12
du_cf_4528 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_4528 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.addr-eq
d_addr'45'eq_4530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_4530 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_4550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'indirect'45'stack_4550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19
                                        ~v20
  = du_sim'45'load'45'indirect'45'stack_4550 v17
du_sim'45'load'45'indirect'45'stack_4550 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'indirect'45'stack_4550 v0
  = coe du_corr'45'clean_4590 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_cleanFlat_4578 v13 v14
du_cleanFlat_4578 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4578 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4580 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4580 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4586 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_corr'45'clean_4590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_corr'45'clean_4590 v17
du_corr'45'clean_4590 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_4590 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_4608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_sim'45'load'45'indirect'45'suc'45'stack_4608 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
                                               ~v16 v17 ~v18 ~v19 ~v20
  = du_sim'45'load'45'indirect'45'suc'45'stack_4608 v17
du_sim'45'load'45'indirect'45'suc'45'stack_4608 ::
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'load'45'indirect'45'suc'45'stack_4608 v0
  = coe du_corr'45'clean_4648 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4636 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_cleanFlat_4636 v13 v14
du_cleanFlat_4636 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4636 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_160
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4638 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4638 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4644 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4644 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1158 -> T_FlatCorr_1056
d_corr'45'clean_4648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_corr'45'clean_4648 v17
du_corr'45'clean_4648 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_4648 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (coe du_keep'45'lo'45'le_1250 (coe v0))
      (coe du_keep'45'stack_1268 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_4664 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_sim'45'store'45'indirect'45'stack_4664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18
                                         ~v19
  = du_sim'45'store'45'indirect'45'stack_4664 v12 v15
du_sim'45'store'45'indirect'45'stack_4664 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'store'45'indirect'45'stack_4664 v0 v1
  = coe du_corr'45'clean_4710 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base
d_base_4690 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> Integer
d_base_4690 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_base_4690 v5 v7 v13
du_base_4690 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) -> AgdaAny -> Integer
du_base_4690 v0 v1 v2
  = coe
      v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Out
d_Out_4692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_Out_4692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_Out_4692 v12
du_Out_4692 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_Out_4692 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_4694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> AgdaAny
d_cf_4694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cf_4694 v12
du_cf_4694 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_4694 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sm-base
d_sm'45'base_4696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_SetsMem_1280
d_sm'45'base_4696 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4700 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_4700 v0 v11 v12
du_cleanFlat_4700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4700 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_792 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v2))
         (coe du_cf_4694 (coe v2)) (coe v1) (coe du_Out_4692 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4702 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4706 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_corr'45'clean_4710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_4710 v12 v15
du_corr'45'clean_4710 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_4710 v0 v1
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v1))
      (d_dom'45'written_1130 (coe v1)) (d_dom'45'sized_1134 (coe v1))
      (coe du_mkeep'45'lo'45'le_1352 (coe v1))
      (coe
         du_windows'45'slot'45'store_3136
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1146 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_4726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_sim'45'store'45'indirect'45'suc'45'stack_4726 ~v0 ~v1 ~v2 ~v3 ~v4
                                                ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16
                                                ~v17 ~v18 ~v19
  = du_sim'45'store'45'indirect'45'suc'45'stack_4726 v12 v15
du_sim'45'store'45'indirect'45'suc'45'stack_4726 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_sim'45'store'45'indirect'45'suc'45'stack_4726 v0 v1
  = coe du_corr'45'clean_4772 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base
d_base_4752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> Integer
d_base_4752 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_base_4752 v5 v7 v13
du_base_4752 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  (AgdaAny -> AgdaAny -> Integer) -> AgdaAny -> Integer
du_base_4752 v0 v1 v2
  = coe
      v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_36
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Out
d_Out_4754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_Out_4754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_Out_4754 v12
du_Out_4754 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_Out_4754 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_4756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> AgdaAny
d_cf_4756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cf_4756 v12
du_cf_4756 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_4756 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sm-base
d_sm'45'base_4758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_SetsMem_1280
d_sm'45'base_4758 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4762 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_4762 v0 v11 v12
du_cleanFlat_4762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4762 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_792 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v2))
         (coe du_cf_4756 (coe v2))
         (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe du_Out_4754 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4764 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4768 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4772 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1280 -> T_FlatCorr_1056
d_corr'45'clean_4772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_4772 v12 v15
du_corr'45'clean_4772 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'clean_4772 v0 v1
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v1))
      (d_dom'45'written_1130 (coe v1)) (d_dom'45'sized_1134 (coe v1))
      (coe du_mkeep'45'lo'45'le_1352 (coe v1))
      (coe
         du_windows'45'slot'45'store_3136
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1146 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.corr-regs-agree
d_corr'45'regs'45'agree_4786 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_1056 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_1056
d_corr'45'regs'45'agree_4786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15 ~v16 ~v17
  = du_corr'45'regs'45'agree_4786 v14
du_corr'45'regs'45'agree_4786 :: T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'regs'45'agree_4786 v0
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v0))
      (d_dom'45'written_1130 (coe v0)) (d_dom'45'sized_1134 (coe v0))
      (d_lo'45'le_1140 (coe v0)) (d_stack'45'eq_1146 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.corr-store-gap
d_corr'45'store'45'gap_4834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_1056 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> T_FlatCorr_1056
d_corr'45'store'45'gap_4834 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 v11 ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'store'45'gap_4834 v0 v1 v11 v15
du_corr'45'store'45'gap_4834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> T_FlatCorr_1056
du_corr'45'store'45'gap_4834 v0 v1 v2 v3
  = coe
      C_constructor_1148 (d_dom'45'fresh_1124 (coe v3))
      (d_dom'45'written_1130 (coe v3)) (d_dom'45'sized_1134 (coe v3))
      (d_lo'45'le_1140 (coe v3))
      (coe
         du_windows'45'store'45'gap_2644 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_578
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
         (coe d_stack'45'eq_1146 (coe v3)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a
d_a_4860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_1056 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer
d_a_4860 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_a_4860 v0 v1 v11
du_a_4860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
du_a_4860 v0 v1 v2
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))))
      (coe
         du_slots_48 (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_580
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.lo≤a
d_lo'8804'a_4862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_1056 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'8804'a_4862 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_lo'8804'a_4862 v0 v11 v15
du_lo'8804'a_4862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'8804'a_4862 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_lo'45'le_1140 (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_576
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1)))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.front≤a
d_front'8804'a_4866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_1056 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'8804'a_4866 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                    ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_front'8804'a_4866 v0 v10 v11 v15
du_front'8804'a_4866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_436 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_1056 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'8804'a_4866 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_front'45'lo_488 (coe v1))
      (coe du_lo'8804'a_4862 (coe v0) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-agree-above
d_ret'45'agree'45'above_4914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'above_4914 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 v19 v20 ~v21 v22 v23 v24
  = du_ret'45'agree'45'above_4914 v0 v1 v10 v16 v19 v20 v22 v23 v24
du_ret'45'agree'45'above_4914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'above_4914 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v9 v10
        -> case coe v4 of
             (:) v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                    -> case coe v17 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                           -> case coe v8 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                  -> case coe v21 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 v6
                                                                 (addInt
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                                       v0 v14)
                                                                    (coe
                                                                       du_slots_48 (coe v1)
                                                                       (coe v15)))
                                                                 (coe v2 v9)
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                    (coe v16)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                                          v0 v14)))
                                                                 v20)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v22)
                                                                 (coe
                                                                    du_ret'45'agree'45'above_4914
                                                                    (coe v0) (coe v1) (coe v2)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                    (coe v12) (coe v10)
                                                                    (coe
                                                                       (\ v24 v25 v26 ->
                                                                          coe
                                                                            v6 v24 v25
                                                                            (coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                  (coe v16)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                                                        v0 v14)))
                                                                               (coe v26))))
                                                                    (coe v19) (coe v23)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> case coe v16 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                           -> case coe v8 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                  -> case coe v20 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              erased
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v21)
                                                                 (coe
                                                                    du_ret'45'agree'45'above_4914
                                                                    (coe v0) (coe v1) (coe v2)
                                                                    (coe v3) (coe v12) (coe v10)
                                                                    (coe
                                                                       (\ v23 v24 v25 ->
                                                                          coe
                                                                            v6 v23 v24
                                                                            (coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                  (coe v15)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                                                        v0 v13)))
                                                                               (coe v25))))
                                                                    (coe v18) (coe v22)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-write-in-frame
d_ret'45'write'45'in'45'frame_5100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_ret'45'write'45'in'45'frame_5100 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19 v20 v21
                                   v22 v23 v24 v25 v26 v27
  = du_ret'45'write'45'in'45'frame_5100
      v0 v1 v10 v15 v17 v20 v21 v22 v23 v24 v25 v26 v27
du_ret'45'write'45'in'45'frame_5100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  Maybe Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_ret'45'write'45'in'45'frame_5100 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                    v10 v11 v12
  = case coe v8 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v13 v14
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                             -> case coe v12 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                    -> case coe v21 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   v10
                                                   (addInt
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                         v0 v5)
                                                      (coe du_slots_48 (coe v1) (coe v6)))
                                                   (coe v2 v13) v9 v20)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v22)
                                                   (coe
                                                      du_ret'45'agree'45'above_4914 (coe v0)
                                                      (coe v1) (coe v2)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                      (coe v7) (coe v14)
                                                      (coe
                                                         (\ v24 v25 v26 ->
                                                            coe
                                                              v10 v24 v25
                                                              (coe
                                                                 MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
                                                                 v4
                                                                 (addInt
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                                       v0 v5)
                                                                    (coe
                                                                       du_slots_48 (coe v1)
                                                                       (coe v6)))
                                                                 v24 v9 v26)))
                                                      (coe v19) (coe v23)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                      -> case coe v16 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> case coe v12 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v21)
                                                   (coe
                                                      du_ret'45'agree'45'above_4914 (coe v0)
                                                      (coe v1) (coe v2) (coe v3) (coe v7) (coe v14)
                                                      (coe
                                                         (\ v23 v24 v25 ->
                                                            coe
                                                              v10 v23 v24
                                                              (coe
                                                                 MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
                                                                 v4
                                                                 (addInt
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                                       v0 v5)
                                                                    (coe
                                                                       du_slots_48 (coe v1)
                                                                       (coe v6)))
                                                                 v23 v9 v25)))
                                                      (coe v18) (coe v22)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-agree-nothing
d_ret'45'agree'45'nothing_5270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'nothing_5270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 v21 v22
  = du_ret'45'agree'45'nothing_5270 v18 v19 v21 v22
du_ret'45'agree'45'nothing_5270 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] -> AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'nothing_5270 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> case coe v3 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                       -> case coe v13 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v14)
                                                      (coe
                                                         du_ret'45'agree'45'nothing_5270 (coe v7)
                                                         (coe v5) (coe v11) (coe v15)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-nil-frames
d_ret'45'nil'45'frames_5370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
d_ret'45'nil'45'frames_5370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_ret'45'nil'45'frames_5370 v15
du_ret'45'nil'45'frames_5370 :: [Integer] -> AgdaAny
du_ret'45'nil'45'frames_5370 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-spill
d_ret'45'spill_5424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  AgdaAny ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_ret'45'spill_5424 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 v22 ~v23 v24
  = du_ret'45'spill_5424 v0 v20 v21 v22 v24
du_ret'45'spill_5424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] -> AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'spill_5424 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v5 v6
        -> case coe v1 of
             []
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                     (coe du_ret'45'nil'45'frames_5370 (coe v6)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             (:) v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                            (coe
                                               du_ret'45'agree'45'nothing_5270 (coe v1) (coe v6)
                                               (coe
                                                  du_windows'45'reanchor_2324
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90
                                                        v0 v9))
                                                  (coe v3))
                                               (coe v14)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a<next
d_a'60'next_5528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_28 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_496 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'60'next_5528 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                 ~v26 ~v27 ~v28 ~v29
  = du_a'60'next_5528 v0 v1 v17 v18
du_a'60'next_5528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'60'next_5528 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
      (coe
         addInt
         (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_90 v0 v2)
         (coe du_slots_48 (coe v1) (coe v3)))
      (coe du_slot'45'size'62'0_60)
