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
import qualified MAlonzo.Code.Agda.Builtin.Float
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
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.FloatBits
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
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_clos'45'reg_32 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_clos'45'reg_32 v5
du_clos'45'reg_32 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_clos'45'reg_32 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_clos'45'reg_40
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.count-reg
d_count'45'reg_34 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_count'45'reg_34 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_count'45'reg_34 v5
du_count'45'reg_34 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_count'45'reg_34 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_count'45'reg_52
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.heap-reg
d_heap'45'reg_36 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_heap'45'reg_36 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_heap'45'reg_36 v5
du_heap'45'reg_36 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_heap'45'reg_36 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_heap'45'reg_42
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.in1-reg
d_in1'45'reg_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_in1'45'reg_38 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_in1'45'reg_38 v5
du_in1'45'reg_38 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_in1'45'reg_38 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in1'45'reg_46
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.in2-reg
d_in2'45'reg_40 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_in2'45'reg_40 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_in2'45'reg_40 v5
du_in2'45'reg_40 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_in2'45'reg_40 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_in2'45'reg_48
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.out-reg
d_out'45'reg_42 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_out'45'reg_42 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_out'45'reg_42 v5
du_out'45'reg_42 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_out'45'reg_42 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_out'45'reg_44
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reg-of
d_reg'45'of_44 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  AgdaAny
d_reg'45'of_44 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_reg'45'of_44 v5
du_reg'45'of_44 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  AgdaAny
du_reg'45'of_44 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.d_reg'45'of_36
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.scratch-reg
d_scratch'45'reg_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_scratch'45'reg_46 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_scratch'45'reg_46 v5
du_scratch'45'reg_46 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_scratch'45'reg_46 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_scratch'45'reg_50
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sp-reg
d_sp'45'reg_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny
d_sp'45'reg_48 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_sp'45'reg_48 v5
du_sp'45'reg_48 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  AgdaAny
du_sp'45'reg_48 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slots
d_slots_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> Integer -> Integer
d_slots_50 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_slots_50 v1 v10
du_slots_50 :: Integer -> Integer -> Integer
du_slots_50 v0 v1 = coe mulInt (coe v1) (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slot-to-disp
d_slot'45'to'45'disp_54 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> Integer -> Integer
d_slot'45'to'45'disp_54 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_slot'45'to'45'disp_54 v1 v10
du_slot'45'to'45'disp_54 :: Integer -> Integer -> Integer
du_slot'45'to'45'disp_54 v0 v1 = coe mulInt (coe v1) (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.nz⇒pos
d_nz'8658'pos_60 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nz'8658'pos_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_nz'8658'pos_60
du_nz'8658'pos_60 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nz'8658'pos_60
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slot-size>0
d_slot'45'size'62'0_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'size'62'0_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_slot'45'size'62'0_62
du_slot'45'size'62'0_62 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'size'62'0_62 = coe du_nz'8658'pos_60
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Word
d_Word_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) -> (AgdaAny -> Bool) -> ()
d_Word_64 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Memory
d_Memory_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) -> (AgdaAny -> Bool) -> ()
d_Memory_66 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.readMem
d_readMem_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_readMem_68 v10 v11
du_readMem_68 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
du_readMem_68 v0 v1 = coe v0 v1
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.writeMem
d_writeMem_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
              v13
  = du_writeMem_74 v10 v11 v12 v13
du_writeMem_74 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
du_writeMem_74 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe eqInt (coe v3) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
      (coe v0 v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.readLoc
d_readLoc_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_readLoc_86
du_readLoc_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_86
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeHeapMem
d_writeHeapMem_88 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_writeHeapMem_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeHeapMem_88
du_writeHeapMem_88 ::
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_writeHeapMem_88
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeHeapMem_850
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeLoc
d_writeLoc_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLoc_90 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeLoc_90 v0
du_writeLoc_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLoc_90 v0
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLoc_878 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeLocToHeap
d_writeLocToHeap_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToHeap_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeLocToHeap_96
du_writeLocToHeap_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToHeap_96
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.writeLocToStack
d_writeLocToStack_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_writeLocToStack_98 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_writeLocToStack_98 v0
du_writeLocToStack_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_writeLocToStack_98 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-load-suc-via-resolved
d_exec'45'load'45'suc'45'via'45'resolved_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'suc'45'via'45'resolved_102 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 ~v8 ~v9
  = du_exec'45'load'45'suc'45'via'45'resolved_102
du_exec'45'load'45'suc'45'via'45'resolved_102 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'suc'45'via'45'resolved_102
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'suc'45'via'45'resolved_1570
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-load-via-resolved
d_exec'45'load'45'via'45'resolved_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'load'45'via'45'resolved_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9
  = du_exec'45'load'45'via'45'resolved_104
du_exec'45'load'45'via'45'resolved_104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractReg_54 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'load'45'via'45'resolved_104
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_exec'45'load'45'via'45'resolved_1532
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-store-suc-via-resolved
d_exec'45'store'45'suc'45'via'45'resolved_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'suc'45'via'45'resolved_108 v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 ~v9
  = du_exec'45'store'45'suc'45'via'45'resolved_108 v0
du_exec'45'store'45'suc'45'via'45'resolved_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'store'45'suc'45'via'45'resolved_108 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'suc'45'via'45'resolved_1582
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-store-via-resolved
d_exec'45'store'45'via'45'resolved_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_exec'45'store'45'via'45'resolved_110 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9
  = du_exec'45'store'45'via'45'resolved_110 v0
du_exec'45'store'45'via'45'resolved_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_exec'45'store'45'via'45'resolved_110 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'store'45'via'45'resolved_1544
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState
d_FlatState_116 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.do-ret
d_do'45'ret_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'ret_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_do'45'ret_144
du_do'45'ret_144 ::
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'ret_144
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_do'45'ret_718
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.do-thunk
d_do'45'thunk_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_do'45'thunk_158 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_do'45'thunk_158 v0
du_do'45'thunk_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_do'45'thunk_158 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_do'45'thunk_852 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.enter-call
d_enter'45'call_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_enter'45'call_160 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_enter'45'call_160 v0
du_enter'45'call_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_enter'45'call_160 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_enter'45'call_538 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.flat-exec-instr
d_flat'45'exec'45'instr_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_flat'45'exec'45'instr_212 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_flat'45'exec'45'instr_212 v0
du_flat'45'exec'45'instr_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_flat'45'exec'45'instr_212 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_flat'45'exec'45'instr_1080
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.leave-frame
d_leave'45'frame_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_leave'45'frame_266
du_leave'45'frame_266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame_266
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame_554
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.leave-frame-aux
d_leave'45'frame'45'aux_268 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame'45'aux_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_leave'45'frame'45'aux_268
du_leave'45'frame'45'aux_268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame'45'aux_268
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.du_leave'45'frame'45'aux_542
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sv-is-zero
d_sv'45'is'45'zero_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_sv'45'is'45'zero_292
du_sv'45'is'45'zero_292 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_292
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_sv'45'is'45'zero_104
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.falloc
d_falloc_310 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_310 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.fclosure
d_fclosure_312 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_312 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.flink
d_flink_314 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Maybe Integer
d_flink_314 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.floc
d_floc_316 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_316 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.fpc
d_fpc_318 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
d_fpc_318 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.FlatState.fret
d_fret_320 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> [Integer]
d_fret_320 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.shift-frame
d_shift'45'frame_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny -> Integer -> AgdaAny
d_shift'45'frame_332 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_shift'45'frame_332 v0
du_shift'45'frame_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> AgdaAny
du_shift'45'frame_332 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sv-below
d_sv'45'below_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_sv'45'below_336 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.svm-below
d_svm'45'below_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> ()
d_svm'45'below_338 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.exec-abstract
d_exec'45'abstract_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'abstract_342 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_exec'45'abstract_342 v0
du_exec'45'abstract_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'abstract_342 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Frame
d_Frame_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) -> (AgdaAny -> Bool) -> ()
d_Frame_350 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.frame-base
d_frame'45'base_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny -> Integer
d_frame'45'base_352 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_frame'45'base_352 v0
du_frame'45'base_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer
du_frame'45'base_352 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.slot-addr
d_slot'45'addr_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> AgdaAny -> Integer -> Integer
d_slot'45'addr_358 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_slot'45'addr_358 v0
du_slot'45'addr_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny -> Integer -> Integer
du_slot'45'addr_358 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView
d_HeapView_362 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_HeapView_362
  = C_mkHV_416 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                Integer)
               Integer (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer)
               (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
               Integer MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.haddr
d_haddr_390 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_390 v0
  = case coe v0 of
      C_mkHV_416 v1 v3 v4 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.HDom
d_HDom_392 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_392 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.hfront
d_hfront_394 :: T_HeapView_362 -> Integer
d_hfront_394 v0
  = case coe v0 of
      C_mkHV_416 v1 v3 v4 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.caddr
d_caddr_396 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_396 v0
  = case coe v0 of
      C_mkHV_416 v1 v3 v4 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.haddr-suc
d_haddr'45'suc_400 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_400 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.haddr-inj
d_haddr'45'inj_406 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_406 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.dom-below
d_dom'45'below_410 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_410 v0
  = case coe v0 of
      C_mkHV_416 v1 v3 v4 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.lo
d_lo_412 :: T_HeapView_362 -> Integer
d_lo_412 v0
  = case coe v0 of
      C_mkHV_416 v1 v3 v4 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.HeapView.front-lo
d_front'45'lo_414 ::
  T_HeapView_362 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_414 v0
  = case coe v0 of
      C_mkHV_416 v1 v3 v4 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.lit-word
d_lit'45'word_418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) -> Integer -> Integer
d_lit'45'word_418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_lit'45'word_418 v10
du_lit'45'word_418 :: Integer -> Integer
du_lit'45'word_418 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.AddrMap
d_AddrMap_422 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_AddrMap_422
  = C_mkAddrMap_432 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                     Integer)
                    (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.AddrMap.hmap
d_hmap_428 ::
  T_AddrMap_422 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_428 v0
  = case coe v0 of
      C_mkAddrMap_432 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.AddrMap.cmap
d_cmap_430 ::
  T_AddrMap_422 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_430 v0
  = case coe v0 of
      C_mkAddrMap_432 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-sv-at
d_enc'45'sv'45'at_434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv'45'at_434 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      v11
  = du_enc'45'sv'45'at_434 v0 v10 v11
du_enc'45'sv'45'at_434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv'45'at_434 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v4 v5
               -> coe
                    MAlonzo.Code.Once.CCC.FrameSemantics.d_slot'45'addr_88 v0 v4 v5
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v4
               -> coe d_hmap_428 v1 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v3 -> coe v3
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_fits'45'int_198 -> coe v5
             MAlonzo.Code.Once.Type.C_fits'45'float_200
               -> coe
                    MAlonzo.Code.Once.Semantics.FloatBits.d_float'45'bits_6 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v3
        -> coe d_cmap_430 v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-maybe-at
d_enc'45'maybe'45'at_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe'45'at_462 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                         v11
  = du_enc'45'maybe'45'at_462 v0 v10 v11
du_enc'45'maybe'45'at_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_AddrMap_422 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe'45'at_462 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_enc'45'sv'45'at_434 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.amap
d_amap_470 :: T_HeapView_362 -> T_AddrMap_422
d_amap_470 v0
  = coe
      C_mkAddrMap_432 (coe d_haddr_390 (coe v0))
      (coe d_caddr_396 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-sv
d_enc'45'sv_474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
d_enc'45'sv_474 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_enc'45'sv_474 v0 v10
du_enc'45'sv_474 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Integer
du_enc'45'sv_474 v0 v1
  = coe
      du_enc'45'sv'45'at_434 (coe v0)
      (coe
         C_mkAddrMap_432 (coe d_haddr_390 (coe v1))
         (coe d_caddr_396 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-maybe
d_enc'45'maybe_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
d_enc'45'maybe_478 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_enc'45'maybe_478 v0 v10
du_enc'45'maybe_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_362 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Maybe Integer
du_enc'45'maybe_478 v0 v1
  = coe
      du_enc'45'maybe'45'at_462 (coe v0)
      (coe
         C_mkAddrMap_432 (coe d_haddr_390 (coe v1))
         (coe d_caddr_396 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.frames-of
d_frames'45'of_482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_frames'45'of_482 v10
du_frames'45'of_482 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_482 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v0))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
            (coe v0)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Window
d_Window_486 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny -> Integer -> ()
d_Window_486 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.StackWindows
d_StackWindows_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_502 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.GapNext
d_GapNext_526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_GapNext_526 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.RetAddrs
d_RetAddrs_536 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer] -> ()
d_RetAddrs_536 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-unlink
d_ret'45'unlink_610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
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
d_ret'45'unlink_610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                    ~v11 ~v12 v13 ~v14 ~v15 ~v16 v17 v18 v19
  = du_ret'45'unlink_610 v10 v13 v17 v18 v19
du_ret'45'unlink_610 ::
  (Integer -> Integer) ->
  Maybe Integer ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_ret'45'unlink_610 v0 v1 v2 v3 v4
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
d_ret'45'relink_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
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
d_ret'45'relink_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                    ~v11 ~v12 v13 ~v14 ~v15 ~v16 v17 v18 v19
  = du_ret'45'relink_696 v10 v13 v17 v18 v19
du_ret'45'relink_696 ::
  (Integer -> Integer) ->
  Maybe Integer ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_ret'45'relink_696 v0 v1 v2 v3 v4
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
d_ret'45'relk_782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
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
d_ret'45'relk_782 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
                  ~v12 ~v13 v14 v15 v16 v17 v18
  = du_ret'45'relk_782 v0 v1 v10 v14 v15 v16 v17 v18
du_ret'45'relk_782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  (Integer -> Integer) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ret'45'relk_782 v0 v1 v2 v3 v4 v5 v6 v7
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
                                                         MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                         v0 v13)
                                                      (coe du_slots_50 (coe v1) (coe v14)))
                                                   (coe v2 v8) v15)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v17)
                                                   (coe
                                                      du_ret'45'relk_782 (coe v0) (coe v1) (coe v2)
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
                                                  du_ret'45'relk_782 (coe v0) (coe v1) (coe v2)
                                                  (coe v3) (coe v11) (coe v9) (coe v6) (coe v15)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-head
d_ret'45'head_888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
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
d_ret'45'head_888 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 v21
  = du_ret'45'head_888 v13 v19 v21
du_ret'45'head_888 ::
  Maybe Integer -> [Integer] -> AgdaAny -> AgdaAny
du_ret'45'head_888 v0 v1 v2
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
d_FlatCorr_982 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_FlatCorr_982
  = C_constructor_1078 (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                       (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny)
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.in1-eq
d_in1'45'eq_1034 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_1034 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.in2-eq
d_in2'45'eq_1036 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in2'45'eq_1036 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.out-eq
d_out'45'eq_1038 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_1038 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.scratch-eq
d_scratch'45'eq_1040 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_1040 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.count-eq
d_count'45'eq_1042 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_1042 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.clos-eq
d_clos'45'eq_1044 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_1044 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.halt-eq
d_halt'45'eq_1046 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_1046 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.sp-eq
d_sp'45'eq_1048 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_1048 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.frontier-eq
d_frontier'45'eq_1050 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_1050 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.dom-fresh
d_dom'45'fresh_1054 ::
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_1054 v0
  = case coe v0 of
      C_constructor_1078 v10 v11 v12 v14 v16 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.dom-written
d_dom'45'written_1060 ::
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_1060 v0
  = case coe v0 of
      C_constructor_1078 v10 v11 v12 v14 v16 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.dom-sized
d_dom'45'sized_1064 ::
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_1064 v0
  = case coe v0 of
      C_constructor_1078 v10 v11 v12 v14 v16 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.heap-eq
d_heap'45'eq_1068 ::
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_1068 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.lo-le
d_lo'45'le_1070 ::
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_1070 v0
  = case coe v0 of
      C_constructor_1078 v10 v11 v12 v14 v16 -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.untouched
d_untouched_1074 ::
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_1074 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.FlatCorr.stack-eq
d_stack'45'eq_1076 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_1076 v0
  = case coe v0 of
      C_constructor_1078 v10 v11 v12 v14 v16 -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole
d_SetsRole_1088 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_SetsRole_1088 = C_constructor_1118
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.at-role
d_at'45'role_1108 ::
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_1108 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.off-role
d_off'45'role_1112 ::
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_1112 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.keeps-mem
d_keeps'45'mem_1114 ::
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_1114 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRole.keeps-halt
d_keeps'45'halt_1116 ::
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_1116 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-in1
d_keep'45'in1_1140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in1_1140 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-in2
d_keep'45'in2_1144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in2_1144 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-out
d_keep'45'out_1148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'out_1148 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-scratch
d_keep'45'scratch_1152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'scratch_1152 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-count
d_keep'45'count_1156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'count_1156 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-clos
d_keep'45'clos_1160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'clos_1160 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-sp
d_keep'45'sp_1164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'sp_1164 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-heap-reg
d_keep'45'heap'45'reg_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap'45'reg_1168 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-halt
d_keep'45'halt_1172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'halt_1172 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-heap
d_keep'45'heap_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap_1176 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-lo-le
d_keep'45'lo'45'le_1184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_keep'45'lo'45'le_1184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_keep'45'lo'45'le_1184 v16
du_keep'45'lo'45'le_1184 ::
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_keep'45'lo'45'le_1184 v0 = coe d_lo'45'le_1070 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-untouched
d_keep'45'untouched_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'untouched_1192 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.keep-stack
d_keep'45'stack_1202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_keep'45'stack_1202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17
  = du_keep'45'stack_1202 v16
du_keep'45'stack_1202 ::
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_keep'45'stack_1202 v0 = coe d_stack'45'eq_1076 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem
d_SetsMem_1214 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_SetsMem_1214 = C_constructor_1248
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.at-addr
d_at'45'addr_1236 ::
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_1236 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.off-addr
d_off'45'addr_1240 ::
  T_SetsMem_1214 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_1240 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.mem-regs
d_mem'45'regs_1244 ::
  T_SetsMem_1214 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_1244 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsMem.mem-halt
d_mem'45'halt_1246 ::
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_1246 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-in1
d_mkeep'45'in1_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in1_1270 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-in2
d_mkeep'45'in2_1272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in2_1272 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-out
d_mkeep'45'out_1274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'out_1274 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-scratch
d_mkeep'45'scratch_1276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'scratch_1276 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-count
d_mkeep'45'count_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'count_1278 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-clos
d_mkeep'45'clos_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'clos_1280 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-sp
d_mkeep'45'sp_1282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'sp_1282 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-heap-reg
d_mkeep'45'heap'45'reg_1284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'heap'45'reg_1284 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-halt
d_mkeep'45'halt_1286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'halt_1286 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.mkeep-lo-le
d_mkeep'45'lo'45'le_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mkeep'45'lo'45'le_1288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17
  = du_mkeep'45'lo'45'le_1288 v16
du_mkeep'45'lo'45'le_1288 ::
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mkeep'45'lo'45'le_1288 v0 = coe d_lo'45'le_1070 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem
d_SetsRoleMem_1304 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
                   a14 a15
  = ()
data T_SetsRoleMem_1304 = C_constructor_1346
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-at-role
d_rm'45'at'45'role_1332 ::
  T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_1332 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-off-role
d_rm'45'off'45'role_1336 ::
  T_SetsRoleMem_1304 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_1336 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-at-addr
d_rm'45'at'45'addr_1338 ::
  T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_1338 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-off-addr
d_rm'45'off'45'addr_1342 ::
  T_SetsRoleMem_1304 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_1342 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.SetsRoleMem.rm-halt
d_rm'45'halt_1344 ::
  T_SetsRoleMem_1304 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_1344 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles
d_Sets2Roles_1360 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
                  a15
  = ()
data T_Sets2Roles_1360 = C_constructor_1398
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.at-role₁
d_at'45'role'8321'_1386 ::
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_1386 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.at-role₂
d_at'45'role'8322'_1388 ::
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_1388 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.off-roles
d_off'45'roles_1392 ::
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_1392 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.keeps-mem₂
d_keeps'45'mem'8322'_1394 ::
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_1394 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.Sets2Roles.keeps-halt₂
d_keeps'45'halt'8322'_1396 ::
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_1396 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.win-at
d_win'45'at_1416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_1416 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.win-off
d_win'45'off_1462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_1462 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.stack-eq-win
d_stack'45'eq'45'win_1498 ::
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_1498 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.stack-eq-cur
d_stack'45'eq'45'cur_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_1512 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sep
d_sep_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_1528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
           v13
  = du_sep_1528 v10 v13
du_sep_1528 ::
  T_HeapView_362 ->
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_1528 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_front'45'lo_414 (coe v0)) (coe d_lo'45'le_1070 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.descend-view
d_descend'45'view_1538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_362
d_descend'45'view_1538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                       v11 ~v12 v13
  = du_descend'45'view_1538 v10 v11 v13
du_descend'45'view_1538 ::
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_362
du_descend'45'view_1538 v0 v1 v2
  = coe
      C_mkHV_416 (d_haddr_390 (coe v0)) (d_hfront_394 (coe v0))
      (d_caddr_396 (coe v0)) (d_dom'45'below_410 (coe v0)) v1 v2
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-descend
d_untouched'45'descend_1562 ::
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_1562 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-mov-to-output
d_sim'45'mov'45'to'45'output_1586 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'mov'45'to'45'output_1586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'mov'45'to'45'output_1586 v14
du_sim'45'mov'45'to'45'output_1586 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'mov'45'to'45'output_1586 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-mov-to-input
d_sim'45'mov'45'to'45'input_1608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'mov'45'to'45'input_1608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'mov'45'to'45'input_1608 v14
du_sim'45'mov'45'to'45'input_1608 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'mov'45'to'45'input_1608 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-mov-input2-to-output
d_sim'45'mov'45'input2'45'to'45'output_1630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'mov'45'input2'45'to'45'output_1630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'mov'45'input2'45'to'45'output_1630 v14
du_sim'45'mov'45'input2'45'to'45'output_1630 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'mov'45'input2'45'to'45'output_1630 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-mov-output-to-input2
d_sim'45'mov'45'output'45'to'45'input2_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'mov'45'output'45'to'45'input2_1652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'mov'45'output'45'to'45'input2_1652 v14
du_sim'45'mov'45'output'45'to'45'input2_1652 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'mov'45'output'45'to'45'input2_1652 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_1676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'tag'45'lit_1676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'load'45'tag'45'lit_1676 v15
du_sim'45'load'45'tag'45'lit_1676 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'tag'45'lit_1676 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_1700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'reg'45'scratch'45'one_1700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'scratch'45'one_1700 v14
du_sim'45'reg'45'scratch'45'one_1700 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'reg'45'scratch'45'one_1700 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_1722 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'reg'45'scratch'45'zero_1722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'scratch'45'zero_1722 v14
du_sim'45'reg'45'scratch'45'zero_1722 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'reg'45'scratch'45'zero_1722 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_1744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'reg'45'count'45'zero_1744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'count'45'zero_1744 v14
du_sim'45'reg'45'count'45'zero_1744 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'reg'45'count'45'zero_1744 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_1766 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'reg'45'scratch'45'load'45'count_1766 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'reg'45'scratch'45'load'45'count_1766 v14
du_sim'45'reg'45'scratch'45'load'45'count_1766 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'reg'45'scratch'45'load'45'count_1766 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sv-tag-zero
d_sv'45'tag'45'zero_1782 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_1782 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-zero
d_enc'45'zero_1790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_1790 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_1806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'indirect'45'suc_1806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_sim'45'load'45'indirect'45'suc_1806 v16
du_sim'45'load'45'indirect'45'suc_1806 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'indirect'45'suc_1806 v0
  = coe du_corr'45'clean_1844 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_1832 v12 v13
du_cleanFlat_1832 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1832 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_1834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1834 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_1840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1840 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_corr'45'clean_1844 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_1844 v16
du_corr'45'clean_1844 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_1844 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect
d_sim'45'load'45'indirect_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'indirect_1860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_sim'45'load'45'indirect_1860 v16
du_sim'45'load'45'indirect_1860 :: T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'indirect_1860 v0
  = coe du_corr'45'clean_1898 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_1886 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1886 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_1886 v12 v13
du_cleanFlat_1886 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1886 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_1888 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_1888 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_1894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1894 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_1898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_corr'45'clean_1898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_1898 v16
du_corr'45'clean_1898 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_1898 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-from-slot
d_sim'45'load'45'from'45'slot_1914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'from'45'slot_1914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_sim'45'load'45'from'45'slot_1914 v16
du_sim'45'load'45'from'45'slot_1914 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'from'45'slot_1914 v0
  = coe du_corr'45'clean_1948 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.ex-eq
d_ex'45'eq_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_1938 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_1942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_1942 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cleanFlat_1942 v12 v13
du_cleanFlat_1942 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_1942 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_1944 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_1944 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_1948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_corr'45'clean_1948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_corr'45'clean_1948 v16
du_corr'45'clean_1948 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_1948 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.≡ᵇ-refl
d_'8801''7495''45'refl_1954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_1954 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_1962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_1962 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-write
d_untouched'45'write_1988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  Integer ->
  T_SetsMem_1214 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_1988 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-heap-store
d_untouched'45'heap'45'store_2016 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_2016 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.untouched-stack-store
d_untouched'45'stack'45'store_2058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_2058 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-heap-eq
d_store'45'heap'45'eq_2098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_SetsMem_1214 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_2098 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-dom-written
d_store'45'dom'45'written_2190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_store'45'dom'45'written_2190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11 ~v12 ~v13 v14 v15 v16 v17 v18
  = du_store'45'dom'45'written_2190 v11 v14 v15 v16 v17 v18
du_store'45'dom'45'written_2190 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_2190 v0 v1 v2 v3 v4 v5
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
d_read'45'write'45'hit_2252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'hit_2252 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.read-write-miss
d_read'45'write'45'miss_2272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
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
d_read'45'write'45'miss_2272 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-reanchor
d_windows'45'reanchor_2304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'reanchor_2304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19
  = du_windows'45'reanchor_2304 v18 v19
du_windows'45'reanchor_2304 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_2304 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             seq (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-lower
d_windows'45'lower_2334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'lower_2334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17
  = du_windows'45'lower_2334 v15 v16 v17
du_windows'45'lower_2334 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'lower_2334 v0 v1 v2
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
d_windows'45'forget_2380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'forget_2380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17
  = du_windows'45'forget_2380 v15 v16 v17
du_windows'45'forget_2380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'forget_2380 v0 v1 v2
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
                                     (coe du_windows'45'forget_2380 (coe v4) erased (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-leave
d_windows'45'leave_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_2434 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                        ~v11 ~v12 v13 ~v14 v15
  = du_windows'45'leave_2434 v0 v13 v15
du_windows'45'leave_2434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_2434 v0 v1 v2
  = coe
      du_go_2454 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v1))
      (coe v2)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_2454 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 v13
          ~v14 ~v15 v16 ~v17 v18
  = du_go_2454 v0 v13 v16 v18
du_go_2454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_2454 v0 v1 v2 v3
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
                                                    MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                    v0
                                                    (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                                                       (coe v1))))
                                              (coe v10)))
                                        (coe v11))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-above
d_windows'45'above_2500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'above_2500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 v19
  = du_windows'45'above_2500 v16 v19
du_windows'45'above_2500 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'above_2500 v0 v1
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
                                 (coe du_windows'45'above_2500 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.up
d_up_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_up_2550 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23
  = du_up_2550 v0 v16 v21
du_up_2550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_up_2550 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.window-store-above
d_window'45'store'45'above_2582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_window'45'store'45'above_2582 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-store-gap
d_windows'45'store'45'gap_2624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'store'45'gap_2624 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17 ~v18 v19
  = du_windows'45'store'45'gap_2624 v0 v1 v15 v16 v17 v19
du_windows'45'store'45'gap_2624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'store'45'gap_2624 v0 v1 v2 v3 v4 v5
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
                                        du_windows'45'lower_2334 (coe v4)
                                        (coe
                                           du_a'8804'next_2684 (coe v0) (coe v1) (coe v2) (coe v3))
                                        (coe
                                           du_windows'45'above_2500 (coe v4)
                                           (coe
                                              du_windows'45'reanchor_2304
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                    v0 v8))
                                              (coe v13)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a
d_a_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_a_2678 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_a_2678 v0 v1 v15 v16
du_a_2678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> AgdaAny -> Integer -> Integer
du_a_2678 v0 v1 v2 v3
  = coe
      addInt
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2)
      (coe du_slots_50 (coe v1) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a<next
d_a'60'next_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'60'next_2680 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_a'60'next_2680 v0 v1 v15 v16
du_a'60'next_2680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'60'next_2680 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
      (coe du_a_2678 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_slot'45'size'62'0_62)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a≤next
d_a'8804'next_2684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'8804'next_2684 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13 ~v14 v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_a'8804'next_2684 v0 v1 v15 v16
du_a'8804'next_2684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'8804'next_2684 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
      (coe du_a'60'next_2680 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-write-below
d_windows'45'write'45'below_2714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_2714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19
  = du_windows'45'write'45'below_2714 v17
du_windows'45'write'45'below_2714 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_2714 v0
  = coe du_windows'45'above_2500 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-heap-store
d_windows'45'heap'45'store_2762 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  T_FlatCorr_982 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_2762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18
  = du_windows'45'heap'45'store_2762 v11 v17
du_windows'45'heap'45'store_2762 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_2762 v0 v1
  = coe
      du_windows'45'write'45'below_2714
      (coe
         du_frames'45'of_482
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
      (d_stack'45'eq_1076 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect
d_sim'45'store'45'indirect_2790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_sim'45'store'45'indirect_2790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_sim'45'store'45'indirect_2790 v11 v12 v15 v17
du_sim'45'store'45'indirect_2790 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> AgdaAny -> T_FlatCorr_982
du_sim'45'store'45'indirect_2790 v0 v1 v2 v3
  = coe du_corr'45'clean_2828 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.v
d_v_2816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_v_2816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_v_2816 v12
du_v_2816 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_v_2816 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_2818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_2818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_2818 v11 v12
du_cleanFlat_2818 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_2818 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))
         (coe v0) (coe du_v_2816 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_2820 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2820 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_2824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2824 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_2828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_corr'45'clean_2828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_corr'45'clean_2828 v11 v12 v15 v17
du_corr'45'clean_2828 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> AgdaAny -> T_FlatCorr_982
du_corr'45'clean_2828 v0 v1 v2 v3
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v2))
      (coe
         du_store'45'dom'45'written_2190 (coe v0) (coe v3)
         (coe d_dom'45'written_1060 (coe v2)))
      (d_dom'45'sized_1064 (coe v2))
      (coe du_mkeep'45'lo'45'le_1288 (coe v2))
      (coe du_windows'45'heap'45'store_2762 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_2842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_sim'45'store'45'indirect'45'suc_2842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_sim'45'store'45'indirect'45'suc_2842 v11 v12 v15 v17
du_sim'45'store'45'indirect'45'suc_2842 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> AgdaAny -> T_FlatCorr_982
du_sim'45'store'45'indirect'45'suc_2842 v0 v1 v2 v3
  = coe du_corr'45'clean_2880 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.v
d_v_2868 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_v_2868 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_v_2868 v12
du_v_2868 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_v_2868 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_2870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_2870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_2870 v11 v12
du_cleanFlat_2870 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_2870 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeLocToHeap_870
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe du_v_2868 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_2872 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_2872 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_2876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2876 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_2880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_corr'45'clean_2880 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19
  = du_corr'45'clean_2880 v11 v12 v15 v17
du_corr'45'clean_2880 ::
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> AgdaAny -> T_FlatCorr_982
du_corr'45'clean_2880 v0 v1 v2 v3
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v2))
      (coe
         du_store'45'dom'45'written_2190
         (coe MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v0))
         (coe v3) (coe d_dom'45'written_1060 (coe v2)))
      (d_dom'45'sized_1064 (coe v2))
      (coe du_mkeep'45'lo'45'le_1288 (coe v2))
      (coe du_windows'45'heap'45'store_2762 (coe v1) (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-restore-input
d_sim'45'restore'45'input_2896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'restore'45'input_2896 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_sim'45'restore'45'input_2896 v16
du_sim'45'restore'45'input_2896 :: T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'restore'45'input_2896 v0
  = coe du_corr'45'clean_2930 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.ex-eq
d_ex'45'eq_2920 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex'45'eq_2920 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_2924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_2924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cleanFlat_2924 v12 v13
du_cleanFlat_2924 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_2924 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_2926 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_2926 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_2930 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_corr'45'clean_2930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_corr'45'clean_2930 v16
du_corr'45'clean_2930 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_2930 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.slot-addr-inj
d_slot'45'addr'45'inj_2940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_2940 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.atstack-slot-inj
d_atstack'45'slot'45'inj_2956 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_2956 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.atstack-frame-inj
d_atstack'45'frame'45'inj_2968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
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
d_atstack'45'frame'45'inj_2968 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_2988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  T_SetsMem_1214 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_2988 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_3040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_SetsMem_1214 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_3040 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.just-inj
d_just'45'inj_3080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_SetsMem_1214 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_3080 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_3082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  T_SetsMem_1214 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3082 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-slot-store
d_windows'45'slot'45'store_3116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_3116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21 v22
  = du_windows'45'slot'45'store_3116 v19 v22
du_windows'45'slot'45'store_3116 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_3116 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe du_windows'45'above_2500 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.waddr
d_waddr_3152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> Integer
d_waddr_3152 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24
  = du_waddr_3152 v0 v1 v14 v16
du_waddr_3152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> AgdaAny -> Integer -> Integer
du_waddr_3152 v0 v1 v2 v3
  = coe
      addInt
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2)
      (coe du_slot'45'to'45'disp_54 (coe v1) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.w<fl
d_w'60'fl_3154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_w'60'fl_3154 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
               ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
  = du_w'60'fl_3154 v0 v1 v14 v15 v16 v21
du_w'60'fl_3154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_w'60'fl_3154 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
         (coe v1) (coe v4) (coe v3) (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base<
d_base'60'_3158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_base'60'_3158 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 v14 v15 v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24 v25
                v26
  = du_base'60'_3158 v0 v1 v14 v15 v16 v21 v25 v26
du_base'60'_3158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_base'60'_3158 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2)
      (addInt
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v8 v9 -> v9) (\ v8 -> mulInt (coe v8) (coe v1)) (0 :: Integer)
            v3)
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2))
      (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v6)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
         (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2)
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
            (coe v1) (coe (0 :: Integer)) (coe v3)
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'691'_6712
               (0 :: Integer) v4 v3 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
               v5)))
      v7
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-at-slot
d_sim'45'store'45'at'45'slot_3188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_sim'45'store'45'at'45'slot_3188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18
  = du_sim'45'store'45'at'45'slot_3188 v12 v15
du_sim'45'store'45'at'45'slot_3188 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'store'45'at'45'slot_3188 v0 v1
  = coe du_corr'45'clean_3222 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base
d_base_3212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> Integer
d_base_3212 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_base_3212 v5 v7 v13
du_base_3212 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) -> AgdaAny -> Integer
du_base_3212 v0 v1 v2
  = coe
      v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Out
d_Out_3214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_3214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_Out_3214 v12
du_Out_3214 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_3214 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> AgdaAny
d_cf_3216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cf_3216 v12
du_cf_3216 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3216 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sm-base
d_sm'45'base_3218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_SetsMem_1214
d_sm'45'base_3218 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_3222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_corr'45'clean_3222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18
  = du_corr'45'clean_3222 v12 v15
du_corr'45'clean_3222 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_3222 v0 v1
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v1))
      (d_dom'45'written_1060 (coe v1)) (d_dom'45'sized_1064 (coe v1))
      (coe du_mkeep'45'lo'45'le_1288 (coe v1))
      (coe
         du_windows'45'slot'45'store_3116
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1076 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-alloc-stack
d_sim'45'alloc'45'stack_3242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'alloc'45'stack_3242 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             ~v10 v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_sim'45'alloc'45'stack_3242 v0 v1 v11 v12 v15 v20
du_sim'45'alloc'45'stack_3242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_982
du_sim'45'alloc'45'stack_3242 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v4))
      (d_dom'45'written_1060 (coe v4)) (d_dom'45'sized_1064 (coe v4)) v5
      (coe
         du_windows'45's_3312 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> AgdaAny
d_cf_3274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_cf_3274 v12
du_cf_3274 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3274 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.newbase
d_newbase_3276 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_3276 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.stk
d_stk_3286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stk_3286 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.tail-le
d_tail'45'le_3308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_3308 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                  v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22
  = du_tail'45'le_3308 v0 v1 v11 v12
du_tail'45'le_3308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_3308 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
               (coe du_cf_3274 (coe v3)) v2))
         (coe du_slots_50 (coe v1) (coe v2)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.windows-s
d_windows'45's_3312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45's_3312 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 v20 ~v21 ~v22
  = du_windows'45's_3312 v0 v1 v11 v12 v15 v20
du_windows'45's_3312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45's_3312 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            du_windows'45'reanchor_2304
            (coe du_tail'45'le_3308 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe d_stack'45'eq_1076 (coe v4))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-thunk
d_sim'45'thunk_3344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'thunk_3344 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_sim'45'thunk_3344 v0 v1 v11 v12 v15 v19
du_sim'45'thunk_3344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_982
du_sim'45'thunk_3344 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v4))
      (d_dom'45'written_1060 (coe v4)) (d_dom'45'sized_1064 (coe v4)) v5
      (coe
         du_windows'45's_3438 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> AgdaAny
d_cf_3374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_cf_3374 v12
du_cf_3374 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3374 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.nothing≢just
d_nothing'8802'just_3380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_3380 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.head-window
d_head'45'window_3386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_head'45'window_3386 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.newbase
d_newbase_3428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_3428 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.tail-le
d_tail'45'le_3434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'le_3434 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                  v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_tail'45'le_3434 v0 v1 v11 v12
du_tail'45'le_3434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'le_3434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
      (coe
         addInt
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
               (coe du_cf_3374 (coe v3)) v2))
         (coe du_slots_50 (coe v1) (coe v2)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.windows-s
d_windows'45's_3438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45's_3438 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                    v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_windows'45's_3438 v0 v1 v11 v12 v15 v19
du_windows'45's_3438 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45's_3438 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            du_windows'45'forget_2380
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
            erased
            (coe
               du_windows'45'lower_2334
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
                  (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3)))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                  (coe du_tail'45'le_3434 (coe v0) (coe v1) (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                     (coe
                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
                        (coe du_cf_3374 (coe v3)))))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe d_stack'45'eq_1076 (coe v4)))))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-call-frame
d_sim'45'call'45'frame_3476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'call'45'frame_3476 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13 ~v14 v15 ~v16 ~v17 ~v18 v19 ~v20 ~v21
  = du_sim'45'call'45'frame_3476 v0 v1 v5 v7 v12 v13 v15 v19
du_sim'45'call'45'frame_3476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_FlatCorr_982
du_sim'45'call'45'frame_3476 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v6))
      (d_dom'45'written_1060 (coe v6)) (d_dom'45'sized_1064 (coe v6)) v7
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               du_windows'45'reanchor_2304
               (coe
                  du_tail'45'floor_3516 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v5))
               (coe
                  du_windows'45'above_2500
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe du_cf_3506 (coe v4))
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
                           (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v4))))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
                        (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v4))))
                  (coe
                     du_windows'45'reanchor_2304
                     (coe
                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                        (coe
                           MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
                           (coe du_cf_3506 (coe v4))))
                     (coe d_stack'45'eq_1076 (coe v6)))))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_3506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> AgdaAny
d_cf_3506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_cf_3506 v12
du_cf_3506 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_3506 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.newbase
d_newbase_3508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_newbase_3508 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.tail-floor
d_tail'45'floor_3516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_SetsRole_1088 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_tail'45'floor_3516 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
                     v12 v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
  = du_tail'45'floor_3516 v0 v1 v5 v7 v12 v13
du_tail'45'floor_3516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_tail'45'floor_3516 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            addInt
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
               (coe
                  MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
                  (coe du_cf_3506 (coe v4)) (1 :: Integer)))
            (coe du_slots_50 (coe v1) (coe (0 :: Integer)))))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
            (coe
               v3 v5
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
                  (coe v2)))
            (coe v1))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
            (coe
               v3 v5
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
                  (coe v2)))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-dealloc-stack
d_sim'45'dealloc'45'stack_3560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'dealloc'45'stack_3560 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9
                               ~v10 ~v11 v12 v13 ~v14 v15 ~v16 ~v17
  = du_sim'45'dealloc'45'stack_3560 v0 v5 v7 v12 v13 v15
du_sim'45'dealloc'45'stack_3560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'dealloc'45'stack_3560 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_1078 (\ v6 v7 -> coe d_dom'45'fresh_1054 v5 v6 v7)
      (d_dom'45'written_1060 (coe v5))
      (\ v6 v7 -> coe d_dom'45'sized_1064 v5 v6 v7)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_1070 (coe v5))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               v2 v4
               (coe
                  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
                  (coe v1)))))
      (coe
         du_windows'45'leave_2434 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v3))
         (coe d_stack'45'eq_1076 (coe v5)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-ret
d_sim'45'ret_3608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'ret_3608 v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 v11 ~v12
                  ~v13 v14 v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_sim'45'ret_3608 v0 v1 v5 v7 v11 v14 v15 v17
du_sim'45'ret_3608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'ret_3608 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      C_constructor_1078 (\ v8 v9 -> coe d_dom'45'fresh_1054 v7 v8 v9)
      (d_dom'45'written_1060 (coe v7))
      (\ v8 v9 -> coe d_dom'45'sized_1064 v7 v8 v9)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
         (coe d_lo'45'le_1070 (coe v7))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
               (coe
                  v3 v6
                  (coe
                     MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
                     (coe v2))))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
               (coe
                  addInt (coe du_slots_50 (coe v1) (coe v4))
                  (coe
                     v3 v6
                     (coe
                        MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
                        (coe v2)))))))
      (coe
         du_windows'45'leave_2434 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v5))
         (coe d_stack'45'eq_1076 (coe v7)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-const
d_sim'45'load'45'const_3662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'const_3662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'load'45'const_3662 v15
du_sim'45'load'45'const_3662 :: T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'const_3662 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-const-float
d_sim'45'load'45'const'45'float_3688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'const'45'float_3688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'load'45'const'45'float_3688 v15
du_sim'45'load'45'const'45'float_3688 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'const'45'float_3688 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-code-addr
d_sim'45'load'45'code'45'addr_3716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'code'45'addr_3716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18
  = du_sim'45'load'45'code'45'addr_3716 v16
du_sim'45'load'45'code'45'addr_3716 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'code'45'addr_3716 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_3744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'save'45'closure'45'reg_3744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15
  = du_sim'45'save'45'closure'45'reg_3744 v14
du_sim'45'save'45'closure'45'reg_3744 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'save'45'closure'45'reg_3744 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.inc-enc
d_inc'45'enc_3764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_3764 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.dec-enc
d_dec'45'enc_3774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_AddrMap_422 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_3774 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_3788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'reg'45'count'45'inc_3788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16 ~v17
  = du_sim'45'reg'45'count'45'inc_3788 v15
du_sim'45'reg'45'count'45'inc_3788 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'reg'45'count'45'inc_3788 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_3818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'reg'45'scratch'45'dec_3818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16 ~v17
  = du_sim'45'reg'45'scratch'45'dec_3818 v15
du_sim'45'reg'45'scratch'45'dec_3818 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'reg'45'scratch'45'dec_3818 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-aux
d_ext'45'addr'45'aux_3844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_3844 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 v11 ~v12 v13
  = du_ext'45'addr'45'aux_3844 v1 v10 v11 v13
du_ext'45'addr'45'aux_3844 ::
  Integer ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_3844 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    addInt (coe d_hfront_394 (coe v1))
                    (coe
                       du_slot'45'to'45'disp_54 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v2)))
             else coe seq (coe v5) (coe d_haddr_390 v1 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr
d_ext'45'addr_3862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_3862 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   v12
  = du_ext'45'addr_3862 v1 v10 v11 v12
du_ext'45'addr_3862 ::
  Integer ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_3862 v0 v1 v2 v3
  = coe
      du_ext'45'addr'45'aux_3844 (coe v0) (coe v1) (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v3)))
         (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ExtDom
d_ExtDom_3878 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_ExtDom_3878
  = C_ext'45'old_3888 AgdaAny |
    C_ext'45'fresh_3890 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-old
d_ext'45'addr'45'old_3898 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_3898 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_3914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3914 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-fresh
d_ext'45'addr'45'fresh_3924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_3924 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.go
d_go_3940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_3940 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-addr-base
d_ext'45'addr'45'base_3948 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_3948 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.+-not-<
d_'43''45'not'45''60'_3958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_3958 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-suc-aux
d_ext'45'suc'45'aux_3976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_3976 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ext-suc
d_ext'45'suc_4002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_4002 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.extend-view
d_extend'45'view_4020 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_362
d_extend'45'view_4020 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
                      v11 v12 ~v13 v14
  = du_extend'45'view_4020 v1 v10 v11 v12 v14
du_extend'45'view_4020 ::
  Integer ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_362
du_extend'45'view_4020 v0 v1 v2 v3 v4
  = coe
      C_mkHV_416 (coe du_ext'45'addr_3862 (coe v0) (coe v1) (coe v2))
      (addInt
         (coe d_hfront_394 (coe v1)) (coe du_slots_50 (coe v0) (coe v3)))
      (d_caddr_396 (coe v1))
      (coe du_below_4038 (coe v0) (coe v1) (coe v3)) (d_lo_412 (coe v1))
      v4
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.below
d_below_4038 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3878 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_below_4038 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12
             ~v13 ~v14 v15 v16
  = du_below_4038 v1 v10 v12 v15 v16
du_below_4038 ::
  Integer ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3878 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_below_4038 v0 v1 v2 v3 v4
  = case coe v4 of
      C_ext'45'old_3888 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'60''45'trans'737'_6714
             (coe d_haddr_390 v1 v3) (d_hfront_394 (coe v1))
             (addInt
                (coe d_hfront_394 (coe v1)) (coe du_slots_50 (coe v0) (coe v2)))
             (coe d_dom'45'below_410 v1 v3 v5)
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                (coe d_hfront_394 (coe v1)))
      C_ext'45'fresh_3890 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
             (coe d_hfront_394 (coe v1))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_50 (coe v3))
                (coe v2) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cross
d_cross_4058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
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
d_cross_4058 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.inj
d_inj_4076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3878 ->
  T_ExtDom_3878 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj_4076 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._._.addr-eq
d_addr'45'eq_4126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
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
d_addr'45'eq_4126 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._._.off-eq
d_off'45'eq_4128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
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
d_off'45'eq_4128 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-ext
d_enc'45'ext_4144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_4144 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.enc-ext-maybe
d_enc'45'ext'45'maybe_4228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_4228 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.windows-enc-ext
d_windows'45'enc'45'ext_4278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_windows'45'enc'45'ext_4278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 v20
  = du_windows'45'enc'45'ext_4278 v18 v20
du_windows'45'enc'45'ext_4278 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_4278 v0 v1
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
                                 (coe du_windows'45'enc'45'ext_4278 (coe v3) (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-alloc-heap
d_sim'45'alloc'45'heap_4360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 -> T_FlatCorr_982
d_sim'45'alloc'45'heap_4360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                            ~v24 ~v25
  = du_sim'45'alloc'45'heap_4360 v12 v15
du_sim'45'alloc'45'heap_4360 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'alloc'45'heap_4360 v0 v1
  = coe
      C_constructor_1078 (coe du_df_4436 (coe v0) (coe v1))
      (\ v2 v3 v4 ->
         coe C_ext'45'old_3888 (coe d_dom'45'written_1060 v1 v2 v3 erased))
      (coe du_ds_4404 (coe v0) (coe v1)) (d_lo'45'le_1070 (coe v1))
      (coe
         du_windows'45'enc'45'ext_4278
         (coe
            du_frames'45'of_482
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1076 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.st
d_st_4398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 -> Integer
d_st_4398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_st_4398 v12
du_st_4398 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
du_st_4398 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.dfr
d_dfr_4400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dfr_4400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_dfr_4400 v15
du_dfr_4400 ::
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_dfr_4400 v0 = coe d_dom'45'fresh_1054 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.ds
d_ds_4404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3878
d_ds_4404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
          v27
  = du_ds_4404 v12 v15 v26 v27
du_ds_4404 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3878
du_ds_4404 v0 v1 v2 v3
  = coe
      du_go_4416 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
            (coe
               MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_48 (coe v2)))
         (coe du_st_4398 (coe v0)))
      (coe v3)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._._.go
d_go_4416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3878
d_go_4416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
          ~v27 v28 v29
  = du_go_4416 v15 v26 v28 v29
du_go_4416 ::
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_ExtDom_3878
du_go_4416 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe seq (coe v5) (coe C_ext'45'fresh_3890 v3)
             else coe
                    seq (coe v5)
                    (coe C_ext'45'old_3888 (coe d_dom'45'sized_1064 v0 v1 v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.hv'
d_hv''_4424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 -> T_HeapView_362
d_hv''_4424 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 ~v13
            ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24 ~v25
  = du_hv''_4424 v1 v10 v11 v12 v24
du_hv''_4424 ::
  Integer ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_HeapView_362
du_hv''_4424 v0 v1 v2 v3 v4
  = coe
      du_extend'45'view_4020 (coe v0) (coe v1) (coe du_st_4398 (coe v3))
      (coe v2) (coe v4)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.fresh-x86
d_fresh'45'x86_4428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fresh'45'x86_4428 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.df
d_df_4436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3878 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_df_4436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
          v27
  = du_df_4436 v12 v15 v26 v27
du_df_4436 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3878 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_df_4436 v0 v1 v2 v3
  = case coe v3 of
      C_ext'45'old_3888 v4
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3204
             (coe du_dfr_4400 v1 v2 v4)
      C_ext'45'fresh_3890 v5
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe addInt (coe (1 :: Integer)) (coe du_st_4398 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.hp
d_hp_4446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  AgdaAny ->
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
  T_Sets2Roles_1360 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  T_ExtDom_3878 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_hp_4446 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-lea-slot
d_sim'45'lea'45'slot_4490 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'lea'45'slot_4490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_sim'45'lea'45'slot_4490 v15
du_sim'45'lea'45'slot_4490 :: T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'lea'45'slot_4490 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_4510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny -> AgdaAny -> T_FlatCorr_982 -> T_SetsRole_1088 -> AgdaAny
d_cf_4510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16
  = du_cf_4510 v12
du_cf_4510 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_4510 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.addr-eq
d_addr'45'eq_4512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_addr'45'eq_4512 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_4532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'indirect'45'stack_4532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19
                                        ~v20
  = du_sim'45'load'45'indirect'45'stack_4532 v17
du_sim'45'load'45'indirect'45'stack_4532 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'indirect'45'stack_4532 v0
  = coe du_corr'45'clean_4572 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_cleanFlat_4560 v13 v14
du_cleanFlat_4560 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4560 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4562 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4568 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4568 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4572 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_corr'45'clean_4572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_corr'45'clean_4572 v17
du_corr'45'clean_4572 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_4572 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_4590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_sim'45'load'45'indirect'45'suc'45'stack_4590 ~v0 ~v1 ~v2 ~v3 ~v4
                                               ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
                                               ~v16 v17 ~v18 ~v19 ~v20
  = du_sim'45'load'45'indirect'45'suc'45'stack_4590 v17
du_sim'45'load'45'indirect'45'suc'45'stack_4590 ::
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'load'45'indirect'45'suc'45'stack_4590 v0
  = coe du_corr'45'clean_4630 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20
  = du_cleanFlat_4618 v13 v14
du_cleanFlat_4618 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4618 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_writeReg_168
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60) v0)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v1))))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v1)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v1))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4620 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4626 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SetsRole_1088 -> T_FlatCorr_982
d_corr'45'clean_4630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_corr'45'clean_4630 v17
du_corr'45'clean_4630 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_4630 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (coe du_keep'45'lo'45'le_1184 (coe v0))
      (coe du_keep'45'stack_1202 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_4646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_sim'45'store'45'indirect'45'stack_4646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18
                                         ~v19
  = du_sim'45'store'45'indirect'45'stack_4646 v12 v15
du_sim'45'store'45'indirect'45'stack_4646 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'store'45'indirect'45'stack_4646 v0 v1
  = coe du_corr'45'clean_4692 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base
d_base_4672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> Integer
d_base_4672 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_base_4672 v5 v7 v13
du_base_4672 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) -> AgdaAny -> Integer
du_base_4672 v0 v1 v2
  = coe
      v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Out
d_Out_4674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_4674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_Out_4674 v12
du_Out_4674 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_4674 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_4676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> AgdaAny
d_cf_4676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cf_4676 v12
du_cf_4676 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_4676 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sm-base
d_sm'45'base_4678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_SetsMem_1214
d_sm'45'base_4678 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4682 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_4682 v0 v11 v12
du_cleanFlat_4682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4682 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v2))
         (coe du_cf_4676 (coe v2)) (coe v1) (coe du_Out_4674 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4684 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4688 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_corr'45'clean_4692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_4692 v12 v15
du_corr'45'clean_4692 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_4692 v0 v1
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v1))
      (d_dom'45'written_1060 (coe v1)) (d_dom'45'sized_1064 (coe v1))
      (coe du_mkeep'45'lo'45'le_1288 (coe v1))
      (coe
         du_windows'45'slot'45'store_3116
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1076 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_4708 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_sim'45'store'45'indirect'45'suc'45'stack_4708 ~v0 ~v1 ~v2 ~v3 ~v4
                                                ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13 ~v14 v15 ~v16
                                                ~v17 ~v18 ~v19
  = du_sim'45'store'45'indirect'45'suc'45'stack_4708 v12 v15
du_sim'45'store'45'indirect'45'suc'45'stack_4708 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_sim'45'store'45'indirect'45'suc'45'stack_4708 v0 v1
  = coe du_corr'45'clean_4754 (coe v0) (coe v1)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.base
d_base_4734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> Integer
d_base_4734 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12
            v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_base_4734 v5 v7 v13
du_base_4734 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  (AgdaAny -> AgdaAny -> Integer) -> AgdaAny -> Integer
du_base_4734 v0 v1 v2
  = coe
      v1 v2
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.du_sp'45'reg_38
         (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.Out
d_Out_4736 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_Out_4736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_Out_4736 v12
du_Out_4736 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_Out_4736 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_60)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cf
d_cf_4738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> AgdaAny
d_cf_4738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cf_4738 v12
du_cf_4738 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> AgdaAny
du_cf_4738 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.sm-base
d_sm'45'base_4740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_SetsMem_1214
d_sm'45'base_4740 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.cleanFlat
d_cleanFlat_4744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
d_cleanFlat_4744 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_cleanFlat_4744 v0 v11 v12
du_cleanFlat_4744 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68
du_cleanFlat_4744 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_writeLocToStack_860 (coe v0)
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_floc_82 (coe v2))
         (coe du_cf_4738 (coe v2))
         (coe addInt (coe (1 :: Integer)) (coe v1))
         (coe du_Out_4736 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fpc_86 (coe v2)))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fret_88 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fclosure_90 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_flink_92 (coe v2))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.floc-eq
d_floc'45'eq_4746 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_floc'45'eq_4746 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.reduces
d_reduces_4750 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduces_4750 = erased
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.corr-clean
d_corr'45'clean_4754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_SetsMem_1214 -> T_FlatCorr_982
d_corr'45'clean_4754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'clean_4754 v12 v15
du_corr'45'clean_4754 ::
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'clean_4754 v0 v1
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v1))
      (d_dom'45'written_1060 (coe v1)) (d_dom'45'sized_1064 (coe v1))
      (coe du_mkeep'45'lo'45'le_1288 (coe v1))
      (coe
         du_windows'45'slot'45'store_3116
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v0)))
         (coe d_stack'45'eq_1076 (coe v1)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.corr-regs-agree
d_corr'45'regs'45'agree_4768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  T_FlatCorr_982 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FlatCorr_982
d_corr'45'regs'45'agree_4768 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 v14 ~v15 ~v16 ~v17
  = du_corr'45'regs'45'agree_4768 v14
du_corr'45'regs'45'agree_4768 :: T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'regs'45'agree_4768 v0
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v0))
      (d_dom'45'written_1060 (coe v0)) (d_dom'45'sized_1064 (coe v0))
      (d_lo'45'le_1070 (coe v0)) (d_stack'45'eq_1076 (coe v0))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.corr-store-gap
d_corr'45'store'45'gap_4816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_982 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> T_FlatCorr_982
d_corr'45'store'45'gap_4816 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 v11 ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_corr'45'store'45'gap_4816 v0 v1 v11 v15
du_corr'45'store'45'gap_4816 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> T_FlatCorr_982
du_corr'45'store'45'gap_4816 v0 v1 v2 v3
  = coe
      C_constructor_1078 (d_dom'45'fresh_1054 (coe v3))
      (d_dom'45'written_1060 (coe v3)) (d_dom'45'sized_1064 (coe v3))
      (d_lo'45'le_1070 (coe v3))
      (coe
         du_windows'45'store'45'gap_2624 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2)))
         (coe d_stack'45'eq_1076 (coe v3)))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a
d_a_4842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_982 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> Integer
d_a_4842 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_a_4842 v0 v1 v11
du_a_4842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 -> Integer
du_a_4842 v0 v1 v2
  = coe
      addInt
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))))
      (coe
         du_slots_50 (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
            (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v2))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.lo≤a
d_lo'8804'a_4844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_982 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'8804'a_4844 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_lo'8804'a_4844 v0 v11 v15
du_lo'8804'a_4844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lo'8804'a_4844 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_lo'45'le_1070 (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
         (coe
            MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0
            (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
               (coe MAlonzo.Code.Once.CCC.Machine.Flat.d_falloc_84 (coe v1)))))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.front≤a
d_front'8804'a_4848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  T_FlatCorr_982 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'8804'a_4848 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                    ~v12 ~v13 ~v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_front'8804'a_4848 v0 v10 v11 v15
du_front'8804'a_4848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_HeapView_362 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  T_FlatCorr_982 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_front'8804'a_4848 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe d_front'45'lo_414 (coe v1))
      (coe du_lo'8804'a_4844 (coe v0) (coe v2) (coe v3))
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-agree-above
d_ret'45'agree'45'above_4896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
d_ret'45'agree'45'above_4896 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                             v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 v19 v20 ~v21 v22 v23 v24
  = du_ret'45'agree'45'above_4896 v0 v1 v10 v16 v19 v20 v22 v23 v24
du_ret'45'agree'45'above_4896 ::
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
du_ret'45'agree'45'above_4896 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                                                                       MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                                       v0 v14)
                                                                    (coe
                                                                       du_slots_50 (coe v1)
                                                                       (coe v15)))
                                                                 (coe v2 v9)
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                    (coe v16)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                                          v0 v14)))
                                                                 v20)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v22)
                                                                 (coe
                                                                    du_ret'45'agree'45'above_4896
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
                                                                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
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
                                                                    du_ret'45'agree'45'above_4896
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
                                                                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
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
d_ret'45'write'45'in'45'frame_5082 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
d_ret'45'write'45'in'45'frame_5082 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16 v17 ~v18 ~v19 v20 v21
                                   v22 v23 v24 v25 v26 v27
  = du_ret'45'write'45'in'45'frame_5082
      v0 v1 v10 v15 v17 v20 v21 v22 v23 v24 v25 v26 v27
du_ret'45'write'45'in'45'frame_5082 ::
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
du_ret'45'write'45'in'45'frame_5082 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
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
                                                         MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                         v0 v5)
                                                      (coe du_slots_50 (coe v1) (coe v6)))
                                                   (coe v2 v13) v9 v20)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v22)
                                                   (coe
                                                      du_ret'45'agree'45'above_4896 (coe v0)
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
                                                                       MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                                       v0 v5)
                                                                    (coe
                                                                       du_slots_50 (coe v1)
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
                                                      du_ret'45'agree'45'above_4896 (coe v0)
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
                                                                       MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                                       v0 v5)
                                                                    (coe
                                                                       du_slots_50 (coe v1)
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
d_ret'45'agree'45'nothing_5252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'nothing_5252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 ~v20 v21 v22
  = du_ret'45'agree'45'nothing_5252 v18 v19 v21 v22
du_ret'45'agree'45'nothing_5252 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] -> AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'nothing_5252 v0 v1 v2 v3
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
                                                         du_ret'45'agree'45'nothing_5252 (coe v7)
                                                         (coe v5) (coe v11) (coe v15)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-nil-frames
d_ret'45'nil'45'frames_5352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
d_ret'45'nil'45'frames_5352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 v15 ~v16
  = du_ret'45'nil'45'frames_5352 v15
du_ret'45'nil'45'frames_5352 :: [Integer] -> AgdaAny
du_ret'45'nil'45'frames_5352 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.ret-spill
d_ret'45'spill_5406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
d_ret'45'spill_5406 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 v20 v21 v22 ~v23 v24
  = du_ret'45'spill_5406 v0 v20 v21 v22 v24
du_ret'45'spill_5406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] -> AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'spill_5406 v0 v1 v2 v3 v4
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
                                     (coe du_ret'45'nil'45'frames_5352 (coe v6)))
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
                                               du_ret'45'agree'45'nothing_5252 (coe v1) (coe v6)
                                               (coe
                                                  du_windows'45'reanchor_2304
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86
                                                        v0 v9))
                                                  (coe v3))
                                               (coe v14)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence._.a<next
d_a'60'next_5510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_RegRoles_30 ->
  () ->
  (AgdaAny -> AgdaAny -> Integer) ->
  (AgdaAny -> Integer -> Maybe Integer) ->
  (AgdaAny -> Bool) ->
  (Integer -> Integer) ->
  T_AddrMap_422 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68) ->
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
d_a'60'next_5510 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
                 ~v26 ~v27 ~v28 ~v29
  = du_a'60'next_5510 v0 v1 v17 v18
du_a'60'next_5510 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_a'60'next_5510 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'60'm'43'n_3736
      (coe
         addInt
         (coe MAlonzo.Code.Once.CCC.FrameSemantics.d_frame'45'base_86 v0 v2)
         (coe du_slots_50 (coe v1) (coe v3)))
      (coe du_slot'45'size'62'0_62)
