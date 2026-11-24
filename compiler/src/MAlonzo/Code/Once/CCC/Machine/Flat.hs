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

module MAlonzo.Code.Once.CCC.Machine.Flat where

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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.InstrSlot
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.Flat.FlatMachine.FlatState
d_FlatState_72 a0 = ()
data T_FlatState_72
  = C_mkFlatFull_98 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254
                    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 Integer
                    [Integer] MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62
                    (Maybe Integer)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.floc
d_floc_86 ::
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254
d_floc_86 v0
  = case coe v0 of
      C_mkFlatFull_98 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.falloc
d_falloc_88 ::
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
d_falloc_88 v0
  = case coe v0 of
      C_mkFlatFull_98 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fpc
d_fpc_90 :: T_FlatState_72 -> Integer
d_fpc_90 v0
  = case coe v0 of
      C_mkFlatFull_98 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fret
d_fret_92 :: T_FlatState_72 -> [Integer]
d_fret_92 v0
  = case coe v0 of
      C_mkFlatFull_98 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fclosure
d_fclosure_94 ::
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62
d_fclosure_94 v0
  = case coe v0 of
      C_mkFlatFull_98 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.flink
d_flink_96 :: T_FlatState_72 -> Maybe Integer
d_flink_96 v0
  = case coe v0 of
      C_mkFlatFull_98 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.mkFlat
d_mkFlat_100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  Integer -> T_FlatState_72
d_mkFlat_100 v0 v1 v2
  = coe
      C_mkFlatFull_98 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Machine.Flat.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 -> Bool
d_sv'45'is'45'zero_108 ~v0 v1 = du_sv'45'is'45'zero_108 v1
du_sv'45'is'45'zero_108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 -> Bool
du_sv'45'is'45'zero_108 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v1
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.tag-zf
d_tag'45'zf_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 -> Bool
d_tag'45'zf_110 ~v0 v1 = du_tag'45'zf_110 v1
du_tag'45'zf_110 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 -> Bool
du_tag'45'zf_110 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'is'45'zero_108 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-fault
d_flat'45'fault_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_72 -> T_FlatState_72
d_flat'45'fault_114 ~v0 v1 = du_flat'45'fault_114 v1
du_flat'45'fault_114 :: T_FlatState_72 -> T_FlatState_72
du_flat'45'fault_114 v0
  = coe
      C_mkFlatFull_98
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_286
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_274
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
            (coe d_floc_86 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_280
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_left_282
            (coe d_floc_86 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      (coe d_falloc_88 (coe v0)) (coe d_fpc_90 (coe v0))
      (coe d_fret_92 (coe v0)) (coe d_fclosure_94 (coe v0))
      (coe d_flink_96 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.tag-test
d_tag'45'test_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  Maybe Bool
d_tag'45'test_118 ~v0 v1 = du_tag'45'test_118 v1
du_tag'45'test_118 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  Maybe Bool
du_tag'45'test_118 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v2
               -> case coe v2 of
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v3 v4
                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v3
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v2
               -> case coe v2 of
                    0 -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    _ -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v2 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-at
d_flat'45'read'45'at_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62
d_flat'45'read'45'at_120 ~v0 v1 v2
  = du_flat'45'read'45'at_120 v1 v2
du_flat'45'read'45'at_120 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62
du_flat'45'read'45'at_120 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_526 (coe v0)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62
d_flat'45'read'45'tag_128 v0 v1 v2
  = coe
      du_flat'45'read'45'at_120 (coe v2)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'gate_1538 (coe v0)
         (coe v1) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1258
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_132
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272 (coe v2))
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))))
-- Once.CCC.Machine.Flat.FlatMachine.label-of?
d_label'45'of'63'_134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_134 ~v0 v1 = du_label'45'of'63'_134 v1
du_label'45'of'63'_134 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_134 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.fl-go
d_fl'45'go_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_138 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_fl'45'at_140 (coe v0) (coe du_label'45'of'63'_134 (coe v4))
             (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-at
d_fl'45'at_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_140 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_fl'45'label'45'match_142 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__150 (coe v5)
                (coe v3))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_fl'45'go_138 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-label-match
d_fl'45'label'45'match_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_142 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_fl'45'go_138 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-label
d_find'45'label_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_174 v0 v1 v2
  = coe
      d_fl'45'go_138 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.entry-of?
d_entry'45'of'63'_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
d_entry'45'of'63'_180 ~v0 v1 = du_entry'45'of'63'_180 v1
du_entry'45'of'63'_180 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22
du_entry'45'of'63'_180 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.thunk-part
d_thunk'45'part_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'part_184 ~v0 v1 = du_thunk'45'part_184 v1
du_thunk'45'part_184 ::
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'part_184 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v2
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?
d_thunk'45'of'63'_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_188 ~v0 v1 = du_thunk'45'of'63'_188 v1
du_thunk'45'of'63'_188 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_188 v0
  = coe du_thunk'45'part_184 (coe du_entry'45'of'63'_180 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.entry→thunk
d_entry'8594'thunk_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entry'8594'thunk_196 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-go
d_ft'45'go_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_204 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_ft'45'at_206 (coe v0) (coe du_entry'45'of'63'_180 (coe v4))
             (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-at
d_ft'45'at_206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_206 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_ft'45'match_208 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7473'__228 (coe v5)
                (coe v3))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_ft'45'go_204 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-match
d_ft'45'match_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_208 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_ft'45'go_204 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-entry
d_find'45'entry_240 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Maybe Integer
d_find'45'entry_240 v0 v1 v2
  = coe
      d_ft'45'go_204 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk
d_find'45'thunk_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_246 v0 v1 v2
  = coe
      d_find'45'entry_240 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.find-fn
d_find'45'fn_252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> Maybe Integer
d_find'45'fn_252 v0 v1 v2
  = coe
      d_find'45'entry_240 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.fetch
d_fetch_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418
d_fetch_258 ~v0 v1 v2 = du_fetch_258 v1 v2
du_fetch_258 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418
du_fetch_258 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_fetch_258 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-++-left
d_fetch'45''43''43''45'left_274 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'left_274 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-++-right
d_fetch'45''43''43''45'right_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45''43''43''45'right_310 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-++-miss
d_fl'45'go'45''43''43''45'miss_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'go'45''43''43''45'miss_332 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-at-++-miss
d_fl'45'at'45''43''43''45'miss_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'at'45''43''43''45'miss_344 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-match-++-miss
d_fl'45'match'45''43''43''45'miss_356 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fl'45'match'45''43''43''45'miss_356 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-go-++-miss
d_ft'45'go'45''43''43''45'miss_424 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45''43''43''45'miss_424 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-at-++-miss
d_ft'45'at'45''43''43''45'miss_436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45''43''43''45'miss_436 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-match-++-miss
d_ft'45'match'45''43''43''45'miss_448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45''43''43''45'miss_448 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-go-prefix
d_ft'45'go'45'prefix_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'go'45'prefix_518 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-at-prefix
d_ft'45'at'45'prefix_532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'at'45'prefix_532 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ft-match-prefix
d_ft'45'match'45'prefix_546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'match'45'prefix_546 = erased
-- Once.CCC.Machine.Flat.FlatMachine.just-injℕ
d_just'45'injℕ_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_624 = erased
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?-sound
d_thunk'45'of'63''45'sound_632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_632 ~v0 v1 ~v2 ~v3
  = du_thunk'45'of'63''45'sound_632 v1
du_thunk'45'of'63''45'sound_632 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_632 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v2 v3
               -> coe
                    seq (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.entry-of?-sound
d_entry'45'of'63''45'sound_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'of'63''45'sound_646 ~v0 v1 ~v2 ~v3
  = du_entry'45'of'63''45'sound_646 v1
du_entry'45'of'63''45'sound_646 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'of'63''45'sound_646 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-go-sound
d_ft'45'go'45'sound_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_666 v0 v1 v2 v3 v4 ~v5
  = du_ft'45'go'45'sound_666 v0 v1 v2 v3 v4
du_ft'45'go'45'sound_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_666 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_696 (coe v0) (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_entry'45'of'63'_180 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_696 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_go_696 v0 v1 v2 v3 v4 v5 v7
du_go_696 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_696 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_go'45'm_706 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7473'__228 (coe v7)
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_ft'45'go'45'sound_666 (coe v0) (coe v2) (coe v3)
                      (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_ft'45'go'45'sound_666 (coe v0) (coe v2) (coe v3)
                         (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-m
d_go'45'm_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'm_706 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go'45'm_706 v0 v1 v2 v3 v4 v5 v8
du_go'45'm_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'm_706 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe du_ts_718 (coe v1)))
                   erased))
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_ft'45'go'45'sound_666 (coe v0) (coe v2) (coe v3)
                      (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_ft'45'go'45'sound_666 (coe v0) (coe v2) (coe v3)
                         (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)))))
-- Once.CCC.Machine.Flat.FlatMachine._._.ts
d_ts_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ts_718 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_ts_718 v1
du_ts_718 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ts_718 v0 = coe du_entry'45'of'63''45'sound_646 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine._._.acc≡j
d_acc'8801'j_720 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_720 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.j≡
d_j'8801'_726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'_726 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.fe
d_fe_728 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_728 = erased
-- Once.CCC.Machine.Flat.FlatMachine.label-of?-sound
d_label'45'of'63''45'sound_758 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_758 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-sound
d_fl'45'go'45'sound_774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_774 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'sound_774 v0 v1 v2 v3 v4
du_fl'45'go'45'sound_774 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_774 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_802 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_134 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_802 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_go_802 v0 v2 v3 v4 v5 v7
du_go_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_802 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_go'45'm_810 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__150 (coe v6)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_fl'45'go'45'sound_774 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_fl'45'go'45'sound_774 (coe v0) (coe v1) (coe v2)
                         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-m
d_go'45'm_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'm_810 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go'45'm_810 v0 v2 v3 v4 v5 v8
du_go'45'm_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'm_810 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_fl'45'go'45'sound_774 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_fl'45'go'45'sound_774 (coe v0) (coe v1) (coe v2)
                         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))))
-- Once.CCC.Machine.Flat.FlatMachine._._.acc≡j
d_acc'8801'j_822 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_822 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.j≡
d_j'8801'_828 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'_828 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.fe
d_fe_830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_830 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-sound
d_find'45'label'45'sound_862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_862 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.r
d_r_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_876 v0 v1 v2 v3 ~v4 = du_r_876 v0 v1 v2 v3
du_r_876 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_r_876 v0 v1 v2 v3
  = coe
      du_fl'45'go'45'sound_774 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine._.d
d_d_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_d_878 v0 v1 v2 v3 ~v4 = du_d_878 v0 v1 v2 v3
du_d_878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_d_878 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_r_876 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine._.j≡d
d_j'8801'd_880 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'd_880 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.fe
d_fe_882 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_882 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-entry-sound
d_find'45'entry'45'sound_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'entry'45'sound_894 v0 v1 v2 v3 ~v4
  = du_find'45'entry'45'sound_894 v0 v1 v2 v3
du_find'45'entry'45'sound_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'entry'45'sound_894 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_b_914 (coe v0) (coe v1) (coe v2) (coe v3)) erased
-- Once.CCC.Machine.Flat.FlatMachine._.r
d_r_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_908 v0 v1 v2 v3 ~v4 = du_r_908 v0 v1 v2 v3
du_r_908 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_r_908 v0 v1 v2 v3
  = coe
      du_ft'45'go'45'sound_666 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine._.d
d_d_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_d_910 v0 v1 v2 v3 ~v4 = du_d_910 v0 v1 v2 v3
du_d_910 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Integer -> Integer
du_d_910 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_r_908 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine._.j≡d
d_j'8801'd_912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'd_912 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.b
d_b_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_b_914 v0 v1 v2 v3 ~v4 = du_b_914 v0 v1 v2 v3
du_b_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Integer -> Integer
du_b_914 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_r_908 (coe v0) (coe v1) (coe v2) (coe v3))))
-- Once.CCC.Machine.Flat.FlatMachine._.fe
d_fe_916 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_916 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk-sound
d_find'45'thunk'45'sound_928 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_928 v0 v1 v2 v3 v4
  = coe
      du_find'45'entry'45'sound_894 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v2)) v3
-- Once.CCC.Machine.Flat.FlatMachine.do-jump
d_do'45'jump_934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_72 -> T_FlatState_72
d_do'45'jump_934 ~v0 v1 = du_do'45'jump_934 v1
du_do'45'jump_934 ::
  Maybe Integer -> T_FlatState_72 -> T_FlatState_72
du_do'45'jump_934 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  C_mkFlatFull_98 (coe d_floc_86 (coe v2)) (coe d_falloc_88 (coe v2))
                  (coe v1) (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
                  (coe d_flink_96 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_98
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
                        (coe d_floc_86 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_274
                        (coe d_floc_86 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
                        (coe d_floc_86 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_280
                        (coe d_floc_86 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_left_282
                        (coe d_floc_86 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_faulted_284
                        (coe d_floc_86 (coe v1))))
                  (coe d_falloc_88 (coe v1)) (coe d_fpc_90 (coe v1))
                  (coe d_fret_92 (coe v1)) (coe d_fclosure_94 (coe v1))
                  (coe d_flink_96 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-branch-at
d_do'45'branch'45'at_942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool -> Maybe Integer -> T_FlatState_72 -> T_FlatState_72
d_do'45'branch'45'at_942 ~v0 v1 = du_do'45'branch'45'at_942 v1
du_do'45'branch'45'at_942 ::
  Bool -> Maybe Integer -> T_FlatState_72 -> T_FlatState_72
du_do'45'branch'45'at_942 v0
  = if coe v0
      then coe (\ v1 v2 -> coe du_do'45'jump_934 v1 v2)
      else coe
             (\ v1 v2 ->
                coe
                  C_mkFlatFull_98 (coe d_floc_86 (coe v2)) (coe d_falloc_88 (coe v2))
                  (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
                  (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
                  (coe d_flink_96 (coe v2)))
-- Once.CCC.Machine.Flat.FlatMachine.do-branch
d_do'45'branch_950 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'branch_950 v0 v1 v2 v3 v4
  = coe
      du_do'45'branch'45'at_942 v1
      (d_find'45'label_174 (coe v0) (coe v3) (coe v2)) v4
-- Once.CCC.Machine.Flat.FlatMachine.do-branch-test
d_do'45'branch'45'test_960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'branch'45'test_960 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_do'45'branch_950 (coe v0) (coe v5) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_flat'45'fault_114 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.in-frame
d_in'45'frame_976 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
d_in'45'frame_976 ~v0 v1 v2 = du_in'45'frame_976 v1 v2
du_in'45'frame_976 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
du_in'45'frame_976 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             ltInt (coe v2)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454 (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.slot-ok
d_slot'45'ok_984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
d_slot'45'ok_984 ~v0 v1 v2 = du_slot'45'ok_984 v1 v2
du_slot'45'ok_984 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
du_slot'45'ok_984 v0 v1
  = coe
      du_in'45'frame_976
      (coe
         MAlonzo.Code.Once.CCC.Machine.InstrSlot.d_slot'45'of_8 (coe v0))
      (coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.block-base?
d_block'45'base'63'_990 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
d_block'45'base'63'_990 ~v0 v1 v2 v3
  = du_block'45'base'63'_990 v1 v2 v3
du_block'45'base'63'_990 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
du_block'45'base'63'_990 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v4
           -> case coe v4 of
                MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          eqInt
                          (coe
                             MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'offset_46 (coe v5))
                          (coe (0 :: Integer)))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe
                             eqInt
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_460 v2
                                (MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                   (coe
                                      MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_44
                                      (coe v5))))
                             (coe v0))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe ltInt (coe (0 :: Integer)) (coe v0))
                             (coe
                                MAlonzo.Code.Data.Bool.Base.d_not_22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_freed_462 v2
                                   (MAlonzo.Code.Once.Memory.HeapAddress.d_ref'45'id_12
                                      (coe
                                         MAlonzo.Code.Once.Memory.HeapAddress.d_heap'45'ref_44
                                         (coe v5)))))))
                _ -> coe v3
         _ -> coe v3)
-- Once.CCC.Machine.Flat.FlatMachine.free-ok
d_free'45'ok_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
d_free'45'ok_1002 ~v0 v1 v2 v3 = du_free'45'ok_1002 v1 v2 v3
du_free'45'ok_1002 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
du_free'45'ok_1002 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2484 v4
           -> coe
                du_block'45'base'63'_990 (coe v4)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_132
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272 (coe v1))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
                (coe v2)
         _ -> coe v3)
-- Once.CCC.Machine.Flat.FlatMachine.gate-at
d_gate'45'at_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
d_gate'45'at_1010 ~v0 v1 v2 v3 v4 = du_gate'45'at_1010 v1 v2 v3 v4
du_gate'45'at_1010 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
du_gate'45'at_1010 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             ltInt (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454 (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_free'45'ok_1002 (coe v1) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.gate-ok
d_gate'45'ok_1026 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
d_gate'45'ok_1026 ~v0 v1 v2 v3 = du_gate'45'ok_1026 v1 v2 v3
du_gate'45'ok_1026 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 -> Bool
du_gate'45'ok_1026 v0 v1 v2
  = coe
      du_gate'45'at_1010
      (coe
         MAlonzo.Code.Once.CCC.Machine.InstrSlot.d_slot'45'of_8 (coe v0))
      (coe v0) (coe v1) (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.straight-go
d_straight'45'go_1034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> T_FlatState_72
d_straight'45'go_1034 v0 v1 v2
  = coe
      C_mkFlatFull_98
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_4144
            (coe v0) (coe v1) (coe d_floc_86 (coe v2))
            (coe d_falloc_88 (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_4144
            (coe v0) (coe v1) (coe d_floc_86 (coe v2))
            (coe d_falloc_88 (coe v2))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
      (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
      (coe d_flink_96 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.straight-at
d_straight'45'at_1040 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> T_FlatState_72
d_straight'45'at_1040 v0 v1 v2 v3
  = if coe v1
      then coe d_straight'45'go_1034 (coe v0) (coe v2) (coe v3)
      else coe du_flat'45'fault_114 (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> T_FlatState_72
d_flat'45'step'45'straight_1050 v0 v1 v2
  = coe
      d_straight'45'at_1040 (coe v0)
      (coe
         du_gate'45'ok_1026 (coe v1) (coe d_floc_86 (coe v2))
         (coe d_falloc_88 (coe v2)))
      (coe v1) (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.straight-keeps
d_straight'45'keeps_1062 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_FlatState_72 -> ()) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> AgdaAny -> AgdaAny -> AgdaAny
d_straight'45'keeps_1062 ~v0 ~v1 v2 v3 v4 v5
  = du_straight'45'keeps_1062 v2 v3 v4 v5
du_straight'45'keeps_1062 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> AgdaAny -> AgdaAny -> AgdaAny
du_straight'45'keeps_1062 v0 v1 v2 v3
  = coe
      du_go_1080 (coe v2) (coe v3)
      (coe
         du_gate'45'ok_1026 (coe v0) (coe d_floc_86 (coe v1))
         (coe d_falloc_88 (coe v1)))
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_FlatState_72 -> ()) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> AgdaAny -> AgdaAny -> Bool -> AgdaAny
d_go_1080 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_go_1080 v4 v5 v6
du_go_1080 :: AgdaAny -> AgdaAny -> Bool -> AgdaAny
du_go_1080 v0 v1 v2 = if coe v2 then coe v0 else coe v1
-- Once.CCC.Machine.Flat.FlatMachine.flink-straight
d_flink'45'straight_1086 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'straight_1086 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fret-straight
d_fret'45'straight_1098 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fret'45'straight_1098 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fclosure-straight
d_fclosure'45'straight_1110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fclosure'45'straight_1110 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-nz
d_do'45'nz_1118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'nz_1118 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v3
        -> coe
             du_flat'45'fault_114
             (coe
                C_mkFlatFull_98 (coe d_floc_86 (coe v2)) (coe d_falloc_88 (coe v2))
                (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
                (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
                (coe d_flink_96 (coe v2)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v3
        -> coe
             du_flat'45'fault_114
             (coe
                C_mkFlatFull_98 (coe d_floc_86 (coe v2)) (coe d_falloc_88 (coe v2))
                (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
                (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
                (coe d_flink_96 (coe v2)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_fits'45'int_26
               -> coe
                    d_flat'45'step'45'straight_1050 (coe v0)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2480)
                    (coe v2)
             MAlonzo.Code.Once.Type.C_fits'45'float_28
               -> coe
                    du_flat'45'fault_114
                    (coe
                       C_mkFlatFull_98 (coe d_floc_86 (coe v2)) (coe d_falloc_88 (coe v2))
                       (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
                       (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
                       (coe d_flink_96 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v3
        -> coe
             du_flat'45'fault_114
             (coe
                C_mkFlatFull_98 (coe d_floc_86 (coe v2)) (coe d_falloc_88 (coe v2))
                (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
                (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
                (coe d_flink_96 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.enter-frame
d_enter'45'frame_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
d_enter'45'frame_1130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_464
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_114 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_450
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_450
               (coe v2))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454
               (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_452
            (coe v2)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_456 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_458
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_460 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_freed_462 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.enter-call
d_enter'45'call_1136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
d_enter'45'call_1136 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_464
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_114 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_450
            (coe v1))
         (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_450
               (coe v1))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454
               (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_452
            (coe v1)))
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_456 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_458
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_460 (coe v1))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_freed_462 (coe v1))
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_1140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
d_leave'45'frame'45'aux_1140 ~v0 v1
  = du_leave'45'frame'45'aux_1140 v1
du_leave'45'frame'45'aux_1140 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
du_leave'45'frame'45'aux_1140 v0
  = case coe v0 of
      [] -> coe (\ v1 -> v1)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    (\ v5 ->
                       coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_464 (coe v3)
                         (coe v2) (coe v4)
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_456 (coe v5))
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_458
                            (coe v5))
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_460 (coe v5))
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_freed_462 (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame
d_leave'45'frame_1152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
d_leave'45'frame_1152 ~v0 v1 = du_leave'45'frame_1152 v1
du_leave'45'frame_1152 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
du_leave'45'frame_1152 v0
  = coe
      du_leave'45'frame'45'aux_1140
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_452
         (coe v0))
      v0
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_1158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_1158 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_1176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_1176 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_1194 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_1194 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1206 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1206 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_1222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_1222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_absurd_1222
du_absurd_1222 :: AgdaAny
du_absurd_1222 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_1232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_1232 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_1250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_1250 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1260 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_1270 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_1270 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1280 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_1290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_1290 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1300 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_1308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348) ->
  T_FlatState_72 -> T_FlatState_72
d_flat'45'step'45'frame_1308 v0 v1 v2 v3
  = coe
      C_mkFlatFull_98
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_4144
            (coe v0) (coe v1) (coe d_floc_86 (coe v3))
            (coe d_falloc_88 (coe v3))))
      (coe
         v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_4144
               (coe v0) (coe v1) (coe d_floc_86 (coe v3))
               (coe d_falloc_88 (coe v3)))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v3)))
      (coe d_fret_92 (coe v3)) (coe d_fclosure_94 (coe v3))
      (coe d_flink_96 (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.ret-land
d_ret'45'land_1316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool -> Integer -> [Integer] -> T_FlatState_72 -> T_FlatState_72
d_ret'45'land_1316 ~v0 v1 = du_ret'45'land_1316 v1
du_ret'45'land_1316 ::
  Bool -> Integer -> [Integer] -> T_FlatState_72 -> T_FlatState_72
du_ret'45'land_1316 v0
  = if coe v0
      then coe
             (\ v1 v2 v3 ->
                coe
                  C_mkFlatFull_98 (coe d_floc_86 (coe v3))
                  (coe du_leave'45'frame_1152 (coe d_falloc_88 (coe v3))) (coe v1)
                  (coe v2) (coe d_fclosure_94 (coe v3)) (coe d_flink_96 (coe v3)))
      else coe (\ v1 v2 v3 -> coe du_flat'45'fault_114 (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.do-ret
d_do'45'ret_1330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> [Integer] -> T_FlatState_72 -> T_FlatState_72
d_do'45'ret_1330 ~v0 v1 v2 v3 = du_do'45'ret_1330 v1 v2 v3
du_do'45'ret_1330 ::
  Integer -> [Integer] -> T_FlatState_72 -> T_FlatState_72
du_do'45'ret_1330 v0 v1 v2
  = case coe v1 of
      [] -> coe du_flat'45'fault_114 (coe v2)
      (:) v3 v4
        -> coe
             du_ret'45'land_1316
             (eqInt
                (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454
                   (coe d_falloc_88 (coe v2))))
             v3 v4 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.≡ᵇ-self
d_'8801''7495''45'self_1346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'self_1346 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ret-pass
d_ret'45'pass_1358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ret'45'pass_1358 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ret-fault-[]
d_ret'45'fault'45''91''93'_1386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ret'45'fault'45''91''93'_1386 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-keeps
d_do'45'ret'45'keeps_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_FlatState_72 -> ()) ->
  Integer ->
  [Integer] ->
  T_FlatState_72 ->
  AgdaAny ->
  (Integer ->
   [Integer] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
d_do'45'ret'45'keeps_1410 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_do'45'ret'45'keeps_1410 v2 v3 v4 v5 v6
du_do'45'ret'45'keeps_1410 ::
  Integer ->
  [Integer] ->
  T_FlatState_72 ->
  AgdaAny ->
  (Integer ->
   [Integer] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
du_do'45'ret'45'keeps_1410 v0 v1 v2 v3 v4
  = case coe v1 of
      [] -> coe v3
      (:) v5 v6
        -> coe
             du_to_1442 (coe v5) (coe v6) (coe v3) (coe v4)
             (coe
                eqInt (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454
                   (coe d_falloc_88 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.to
d_to_1442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (T_FlatState_72 -> ()) ->
  Integer ->
  Integer ->
  [Integer] ->
  T_FlatState_72 ->
  AgdaAny ->
  (Integer ->
   [Integer] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_to_1442 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 ~v9
  = du_to_1442 v3 v4 v6 v7 v8
du_to_1442 ::
  Integer ->
  [Integer] ->
  AgdaAny ->
  (Integer ->
   [Integer] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Bool -> AgdaAny
du_to_1442 v0 v1 v2 v3 v4
  = if coe v4 then coe v3 v0 v1 erased erased else coe v2
-- Once.CCC.Machine.Flat.FlatMachine.RetPost
d_RetPost_1450 a0 a1 a2 = ()
data T_RetPost_1450
  = C_rp'45'fault_1456 | C_rp'45'ret_1462 Integer [Integer]
-- Once.CCC.Machine.Flat.FlatMachine.retView
d_retView_1468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_72 -> T_RetPost_1450
d_retView_1468 ~v0 v1 v2 = du_retView_1468 v1 v2
du_retView_1468 :: Integer -> T_FlatState_72 -> T_RetPost_1450
du_retView_1468 v0 v1
  = coe du_go_1480 (coe v0) (coe v1) (coe d_fret_92 (coe v1))
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1480 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_RetPost_1450
d_go_1480 ~v0 v1 v2 v3 ~v4 = du_go_1480 v1 v2 v3
du_go_1480 ::
  Integer -> T_FlatState_72 -> [Integer] -> T_RetPost_1450
du_go_1480 v0 v1 v2
  = case coe v2 of
      [] -> coe C_rp'45'fault_1456
      (:) v3 v4
        -> coe
             du_gate_1496 (coe v3) (coe v4)
             (coe
                eqInt (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454
                   (coe d_falloc_88 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._._.gate
d_gate_1496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_RetPost_1450
d_gate_1496 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 = du_gate_1496 v3 v4 v6
du_gate_1496 :: Integer -> [Integer] -> Bool -> T_RetPost_1450
du_gate_1496 v0 v1 v2
  = if coe v2
      then coe C_rp'45'ret_1462 v0 v1
      else coe C_rp'45'fault_1456
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_1512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_1512 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_1528 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_1546 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_1546 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_1562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_1562 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-alloc
d_do'45'ret'45'alloc_1584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_1584 = erased
-- Once.CCC.Machine.Flat.FlatMachine.grow-frame
d_grow'45'frame_1598 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348
d_grow'45'frame_1598 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_464
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_114 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_450
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_452
         (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_456 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_458
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_460 (coe v2))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_freed_462 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.do-thunk
d_do'45'thunk_1604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_72 -> T_FlatState_72
d_do'45'thunk_1604 v0 v1 v2
  = coe
      C_mkFlatFull_98
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_286
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
            (coe d_floc_86 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_clear'45'frame_582 (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_274
               (coe d_floc_86 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_114 v0
               (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_450
                  (coe d_falloc_88 (coe v2)))
               v1)
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
            (coe d_floc_86 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_278
            (coe d_floc_86 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_280
            (coe d_floc_86 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_left_282
            (coe d_floc_86 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_faulted_284
            (coe d_floc_86 (coe v2))))
      (coe
         d_grow'45'frame_1598 (coe v0) (coe v1) (coe d_falloc_88 (coe v2)))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v2)))
      (coe d_fret_92 (coe v2)) (coe d_fclosure_94 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Machine.Flat.FlatMachine.flat-halt
d_flat'45'halt_1610 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_72 -> T_FlatState_72
d_flat'45'halt_1610 ~v0 v1 = du_flat'45'halt_1610 v1
du_flat'45'halt_1610 :: T_FlatState_72 -> T_FlatState_72
du_flat'45'halt_1610 v0
  = coe
      C_mkFlatFull_98
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_286
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_274
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
            (coe d_floc_86 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_280
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_left_282
            (coe d_floc_86 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_faulted_284
            (coe d_floc_86 (coe v0))))
      (coe d_falloc_88 (coe v0)) (coe d_fpc_90 (coe v0))
      (coe d_fret_92 (coe v0)) (coe d_fclosure_94 (coe v0))
      (coe d_flink_96 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.do-call-at
d_do'45'call'45'at_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_72 -> T_FlatState_72
d_do'45'call'45'at_1614 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkFlatFull_98 (coe d_floc_86 (coe v3))
                  (coe d_enter'45'call_1136 (coe v0) (coe d_falloc_88 (coe v3)))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v3)))
                     (coe d_fret_92 (coe v3)))
                  (coe d_fclosure_94 (coe v3))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v3)))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe du_flat'45'fault_114 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call-code
d_do'45'call'45'code_1622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'call'45'code_1622 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v5
               -> coe du_flat'45'fault_114 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v5
               -> coe du_flat'45'fault_114 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v5 v6 v7
               -> coe du_flat'45'fault_114 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v5
               -> coe
                    d_do'45'call'45'at_1614 v0
                    (d_find'45'thunk_246 (coe v0) (coe v1) (coe v5)) v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_flat'45'fault_114 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call-sv
d_do'45'call'45'sv_1646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'call'45'sv_1646 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe du_flat'45'fault_114 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    d_do'45'call'45'code_1622 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
                       (d_floc_86 (coe v3))
                       (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v5)))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v4
        -> coe du_flat'45'fault_114 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v4 v5 v6
        -> coe du_flat'45'fault_114 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v4
        -> coe du_flat'45'fault_114 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call
d_do'45'call_1670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'call_1670 v0 v1 v2
  = coe
      d_do'45'call'45'sv_1646 (coe v0) (coe v1)
      (coe d_fclosure_94 (coe v2)) (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.CallPost
d_CallPost_1680 a0 a1 a2 = ()
data T_CallPost_1680
  = C_cp'45'fault_1686 |
    C_cp'45'enter_1694 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 Integer
                       MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38
-- Once.CCC.Machine.Flat.FlatMachine.callView
d_callView_1700 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_CallPost_1680
d_callView_1700 v0 v1 v2
  = coe
      du_go'45'sv_1808 (coe v0) (coe v1) (coe v2)
      (coe d_fclosure_94 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine._.go-at
d_go'45'at_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_1680
d_go'45'at_1716 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_go'45'at_1716 v3 v4 v5
du_go'45'at_1716 ::
  Maybe Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_CallPost_1680
du_go'45'at_1716 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe C_cp'45'enter_1694 v2 v3 v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_cp'45'fault_1686
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-code
d_go'45'code_1756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_1680
d_go'45'code_1756 v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_go'45'code_1756 v0 v1 v3 v4
du_go'45'code_1756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_38 ->
  T_CallPost_1680
du_go'45'code_1756 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v5
               -> coe C_cp'45'fault_1686
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v5
               -> coe C_cp'45'fault_1686
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v5 v6 v7
               -> coe C_cp'45'fault_1686
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v5
               -> coe
                    du_go'45'at_1716
                    (coe d_find'45'thunk_246 (coe v0) (coe v1) (coe v5)) (coe v3)
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_cp'45'fault_1686
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-sv
d_go'45'sv_1808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_1680
d_go'45'sv_1808 v0 v1 v2 v3 ~v4 = du_go'45'sv_1808 v0 v1 v2 v3
du_go'45'sv_1808 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_CallPost_1680
du_go'45'sv_1808 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe C_cp'45'fault_1686
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_go'45'code_1756 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
                       (d_floc_86 (coe v2))
                       (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v5)))
                    (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v4
        -> coe C_cp'45'fault_1686
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v4 v5 v6
        -> coe C_cp'45'fault_1686
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v4
        -> coe C_cp'45'fault_1686
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fault≢
d_fault'8802'_1832 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fault'8802'_1832 = erased
-- Once.CCC.Machine.Flat.FlatMachine.call-ok
d_call'45'ok_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'ok_1844 v0 v1 v2 ~v3 = du_call'45'ok_1844 v0 v1 v2
du_call'45'ok_1844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'ok_1844 v0 v1 v2
  = coe du_go_1862 (coe d_callView_1700 (coe v0) (coe v1) (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CallPost_1680 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1862 ~v0 ~v1 ~v2 ~v3 v4 = du_go_1862 v4
du_go_1862 ::
  T_CallPost_1680 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1862 v0
  = case coe v0 of
      C_cp'45'fault_1686
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      C_cp'45'enter_1694 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ret-ok
d_ret'45'ok_1890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ret'45'ok_1890 ~v0 v1 v2 ~v3 = du_ret'45'ok_1890 v1 v2
du_ret'45'ok_1890 ::
  Integer -> T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ret'45'ok_1890 v0 v1
  = coe du_go_1906 (coe du_retView_1468 (coe v0) (coe v1))
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1906 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RetPost_1450 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1906 ~v0 ~v1 ~v2 ~v3 v4 = du_go_1906 v4
du_go_1906 ::
  T_RetPost_1450 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1906 v0
  = case coe v0 of
      C_rp'45'fault_1456
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      C_rp'45'ret_1462 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.straight-pass
d_straight'45'pass_1924 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_straight'45'pass_1924 = erased
-- Once.CCC.Machine.Flat.FlatMachine.straight-ok
d_straight'45'ok_1938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_straight'45'ok_1938 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_1952 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1952 = erased
-- Once.CCC.Machine.Flat.FlatMachine.slot-in
d_slot'45'in_1968 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'in_1968 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_slot'45'in_1968 v4
du_slot'45'in_1968 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'in_1968 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2824
      (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.slot-ok-in
d_slot'45'ok'45'in_1992 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'ok'45'in_1992 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.T-true
d_T'45'true_2012 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_254 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'45'true_2012 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightPost
d_StraightPost_2020 a0 a1 a2 = ()
data T_StraightPost_2020 = C_sp'45'fault_2026 | C_sp'45'go_2028
-- Once.CCC.Machine.Flat.FlatMachine.straightView
d_straightView_2034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> T_StraightPost_2020
d_straightView_2034 ~v0 v1 v2 = du_straightView_2034 v1 v2
du_straightView_2034 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 -> T_StraightPost_2020
du_straightView_2034 v0 v1
  = coe
      du_go_2046
      (coe
         du_gate'45'ok_1026 (coe v0) (coe d_floc_86 (coe v1))
         (coe d_falloc_88 (coe v1)))
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_2046 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_StraightPost_2020
d_go_2046 ~v0 ~v1 ~v2 v3 ~v4 = du_go_2046 v3
du_go_2046 :: Bool -> T_StraightPost_2020
du_go_2046 v0
  = if coe v0 then coe C_sp'45'go_2028 else coe C_sp'45'fault_2026
-- Once.CCC.Machine.Flat.FlatMachine.do-save-closure
d_do'45'save'45'closure_2054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_72 -> T_FlatState_72
d_do'45'save'45'closure_2054 ~v0 v1
  = du_do'45'save'45'closure_2054 v1
du_do'45'save'45'closure_2054 :: T_FlatState_72 -> T_FlatState_72
du_do'45'save'45'closure_2054 v0
  = coe
      C_mkFlatFull_98 (coe d_floc_86 (coe v0)) (coe d_falloc_88 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v0)))
      (coe d_fret_92 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_132
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
            (coe d_floc_86 (coe v0)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe d_flink_96 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_2058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_flat'45'exec'45'instr_2058 v0 v1
  = let v2
          = \ v2 v3 ->
              d_flat'45'step'45'straight_1050 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2440 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_1308
                     (coe v0) (coe v1) (coe d_enter'45'frame_1130 (coe v0) (coe v3))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2442 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_1308
                     (coe v0) (coe v1) (coe du_leave'45'frame_1152) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2446 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_1308
                     (coe v0) (coe v1)
                     (coe
                        d_enter'45'frame_1130 (coe v0)
                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2448
           -> coe
                (\ v3 v4 ->
                   d_flat'45'step'45'frame_1308
                     (coe v0) (coe v1) (coe du_leave'45'frame_1152) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2450
           -> coe (\ v3 v4 -> d_do'45'call_1670 (coe v0) (coe v3) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2474
           -> coe (\ v3 v4 -> coe du_do'45'save'45'closure_2054 (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2480
           -> coe
                (\ v4 v5 ->
                   d_do'45'nz_1118
                     (coe v0)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_132
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
                           (coe d_floc_86 (coe v5)))
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            C_mkFlatFull_98 (coe d_floc_86 (coe v6)) (coe d_falloc_88 (coe v6))
                            (coe addInt (coe (1 :: Integer)) (coe d_fpc_90 (coe v6)))
                            (coe d_fret_92 (coe v6)) (coe d_fclosure_94 (coe v6))
                            (coe d_flink_96 (coe v6)))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            du_do'45'jump_934 (d_find'45'label_174 (coe v0) (coe v5) (coe v4))
                            v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v4
                  -> coe
                       (\ v5 v6 ->
                          d_do'45'branch'45'test_960
                            (coe v0)
                            (coe
                               du_tag'45'test_118
                               (coe
                                  d_flat'45'read'45'tag_128 (coe v0) (coe d_falloc_88 (coe v6))
                                  (coe d_floc_86 (coe v6))))
                            (coe v4) (coe v5) (coe v6))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v4 v5
                  -> coe (\ v6 v7 -> d_do'45'thunk_1604 (coe v0) (coe v5) (coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v4
                  -> coe
                       (\ v5 v6 ->
                          coe du_do'45'ret_1330 (coe v4) (coe d_fret_92 (coe v6)) (coe v6))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'call'45'at_1614 v0
                            (d_find'45'fn_252 (coe v0) (coe v5) (coe v4)) v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v4
                  -> coe (\ v5 v6 -> d_do'45'thunk_1604 (coe v0) (coe v4) (coe v6))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
                  -> coe
                       (\ v4 v5 ->
                          coe
                            C_mkFlatFull_98
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_286
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
                                  (coe d_floc_86 (coe v5)))
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_274
                                  (coe d_floc_86 (coe v5)))
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
                                  (coe d_floc_86 (coe v5)))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_280
                                  (coe d_floc_86 (coe v5)))
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_faulted_284
                                  (coe d_floc_86 (coe v5))))
                            (coe d_falloc_88 (coe v5)) (coe d_fpc_90 (coe v5))
                            (coe d_fret_92 (coe v5)) (coe d_fclosure_94 (coe v5))
                            (coe d_flink_96 (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.Shifted
d_Shifted_2120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_72 -> T_FlatState_72 -> ()
d_Shifted_2120 = erased
-- Once.CCC.Machine.Flat.FlatMachine.ProgFree
d_ProgFree_2132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 -> ()
d_ProgFree_2132 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shifted-straight
d_shifted'45'straight_2142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'straight_2142 ~v0 ~v1 v2 ~v3 v4 v5
  = du_shifted'45'straight_2142 v2 v4 v5
du_shifted'45'straight_2142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'straight_2142 v0 v1 v2
  = coe
      du_at_2160
      (coe
         du_gate'45'ok_1026 (coe v0) (coe d_floc_86 (coe v1))
         (coe d_falloc_88 (coe v1)))
      (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine._.at
d_at_2160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_2160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_at_2160 v6 v7
du_at_2160 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_2160 v0 v1
  = if coe v0
      then case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                    -> coe
                                         seq (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                  (coe v7))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      else (case coe v1 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
                -> case coe v3 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                       -> case coe v5 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                              -> case coe v7 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                     -> coe
                                          seq (coe v9)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             (coe v3))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.Flat.FlatMachine.shifted-label
d_shifted'45'label_2204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'label_2204 ~v0 ~v1 ~v2 ~v3 v4
  = du_shifted'45'label_2204 v4
du_shifted'45'label_2204 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'label_2204 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                           (coe v6))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-leave
d_shifted'45'leave_2230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'leave_2230 ~v0 ~v1 ~v2 ~v3 v4
  = du_shifted'45'leave_2230 v4
du_shifted'45'leave_2230 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'leave_2230 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  seq (coe v8)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v2))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-thunk
d_shifted'45'thunk_2260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'thunk_2260 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_shifted'45'thunk_2260 v5
du_shifted'45'thunk_2260 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'thunk_2260 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased (coe v10)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-ret-aux
d_shifted'45'ret'45'aux_2300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret'45'aux_2300 ~v0 ~v1 v2 ~v3 v4 v5 ~v6 v7 ~v8
  = du_shifted'45'ret'45'aux_2300 v2 v4 v5 v7
du_shifted'45'ret'45'aux_2300 ::
  Integer ->
  [Integer] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret'45'aux_2300 v0 v1 v2 v3
  = case coe v1 of
      []
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe v5))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                    -> coe
                                         seq (coe v13)
                                         (coe
                                            du_to_2360 erased erased erased erased erased erased
                                            (coe
                                               eqInt (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_454
                                                  (coe d_falloc_88 (coe v2)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.to
d_to_2360 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_to_2360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12 v13 ~v14
          ~v15
  = du_to_2360 v7 v8 v9 v10 v11 v12 v13
du_to_2360 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_to_2360 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))))
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5)))))
-- Once.CCC.Machine.Flat.FlatMachine.shifted-ret
d_shifted'45'ret_2374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'ret_2374 ~v0 ~v1 v2 v3 v4 v5
  = du_shifted'45'ret_2374 v2 v3 v4 v5
du_shifted'45'ret_2374 ::
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'ret_2374 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  seq (coe v11)
                                  (coe
                                     du_shifted'45'ret'45'aux_2300 (coe v0) (coe d_fret_92 (coe v2))
                                     (coe v1) (coe v3))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-jump
d_shifted'45'jump_2400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'jump_2400 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7
  = du_shifted'45'jump_2400 v3 v6
du_shifted'45'jump_2400 ::
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'jump_2400 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         seq (coe v10)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                  (coe v8))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                    -> coe
                                         seq (coe v9)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            (coe v3))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-branch
d_shifted'45'branch_2458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Bool ->
  Bool ->
  Maybe Integer ->
  Maybe Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'branch_2458 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_shifted'45'branch_2458 v2 v5 v8
du_shifted'45'branch_2458 ::
  Bool ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'branch_2458 v0 v1 v2
  = if coe v0
      then coe du_shifted'45'jump_2400 (coe v1) (coe v2)
      else coe du_shifted'45'label_2204 (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.shifted-frame
d_shifted'45'frame_2496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_348) ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'frame_2496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_shifted'45'frame_2496 v6
du_shifted'45'frame_2496 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'frame_2496 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                           (coe v6))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-save-closure
d_shifted'45'save'45'closure_2534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'save'45'closure_2534 ~v0 ~v1 ~v2 ~v3 v4
  = du_shifted'45'save'45'closure_2534 v4
du_shifted'45'save'45'closure_2534 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'save'45'closure_2534 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v9) erased))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-halt
d_shifted'45'halt_2562 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'halt_2562 ~v0 ~v1 ~v2 ~v3 v4
  = du_shifted'45'halt_2562 v4
du_shifted'45'halt_2562 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'halt_2562 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  seq (coe v8)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v2))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-fault
d_shifted'45'fault_2590 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'fault_2590 ~v0 ~v1 ~v2 ~v3 v4
  = du_shifted'45'fault_2590 v4
du_shifted'45'fault_2590 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'fault_2590 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  seq (coe v8)
                                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v2))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-call-at
d_shifted'45'call'45'at_2624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe Integer ->
  Maybe Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'at_2624 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7
  = du_shifted'45'call'45'at_2624 v3 v6
du_shifted'45'call'45'at_2624 ::
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'at_2624 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> case coe v8 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                    -> case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      erased
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            erased (coe v12)))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_shifted'45'fault_2590 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-call-code
d_shifted'45'call'45'code_2672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'code_2672 v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8
  = du_shifted'45'call'45'code_2672 v0 v2 v4 v8
du_shifted'45'call'45'code_2672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'code_2672 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v5
               -> coe du_shifted'45'fault_2590 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v5
               -> coe du_shifted'45'fault_2590 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v5 v6 v7
               -> coe du_shifted'45'fault_2590 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v5
               -> coe
                    du_shifted'45'call'45'at_2624
                    (coe d_find'45'thunk_246 (coe v0) (coe v2) (coe v5)) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_shifted'45'fault_2590 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-call-sv
d_shifted'45'call'45'sv_2754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'sv_2754 v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_shifted'45'call'45'sv_2754 v0 v2 v4 v5 v8
du_shifted'45'call'45'sv_2754 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'sv_2754 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v5
        -> case coe v5 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v6 v7
               -> coe du_shifted'45'fault_2590 (coe v4)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v6
               -> coe
                    seq (coe v4)
                    (coe
                       du_shifted'45'call'45'code_2672 (coe v0)
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
                          (d_floc_86 (coe v3))
                          (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_84 (coe v6)))
                       (coe v2) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v5
        -> coe du_shifted'45'fault_2590 (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v5 v6 v7
        -> coe du_shifted'45'fault_2590 (coe v4)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v5
        -> coe du_shifted'45'fault_2590 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-call-closure
d_shifted'45'call'45'closure_2840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'call'45'closure_2840 v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7
  = du_shifted'45'call'45'closure_2840 v0 v3 v4 v7
du_shifted'45'call'45'closure_2840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'call'45'closure_2840 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  seq (coe v11)
                                  (coe
                                     du_shifted'45'call'45'sv_2754 (coe v0)
                                     (coe d_fclosure_94 (coe v2)) (coe v1) (coe v2) (coe v3))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-test
d_shifted'45'test_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Maybe Bool ->
  Maybe Bool ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'test_2878 v0 ~v1 v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_shifted'45'test_2878 v0 v2 v4 v5 v9
du_shifted'45'test_2878 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Maybe Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'test_2878 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_shifted'45'branch_2458 (coe v5)
             (coe d_find'45'label_174 (coe v0) (coe v2) (coe v1)) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_shifted'45'fault_2590 (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-nz
d_shifted'45'nz_2922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'nz_2922 ~v0 ~v1 v2 ~v3 v4 v5
  = du_shifted'45'nz_2922 v2 v4 v5
du_shifted'45'nz_2922 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'nz_2922 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_66 v3
        -> coe
             du_shifted'45'fault_2590 (coe du_shifted'45'label_2204 (coe v2))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_68 v3
        -> coe
             du_shifted'45'fault_2590 (coe du_shifted'45'label_2204 (coe v2))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_72 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_fits'45'int_26
               -> coe
                    du_shifted'45'straight_2142
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2480)
                    (coe v1) (coe v2)
             MAlonzo.Code.Once.Type.C_fits'45'float_28
               -> coe
                    du_shifted'45'fault_2590 (coe du_shifted'45'label_2204 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_74 v3
        -> coe
             du_shifted'45'fault_2590 (coe du_shifted'45'label_2204 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.shifted-instr
d_shifted'45'instr_2984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'instr_2984 v0 ~v1 v2 ~v3 v4 v5 v6 ~v7 ~v8 v9
  = du_shifted'45'instr_2984 v0 v2 v4 v5 v6 v9
du_shifted'45'instr_2984 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'instr_2984 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2420
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2422
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2424
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2426
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2428 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2430 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2432
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2434
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2436 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2438 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2440 v6
        -> coe du_shifted'45'frame_2496 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2442 v6
        -> coe du_shifted'45'frame_2496 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2444 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2446 v6
        -> coe du_shifted'45'frame_2496 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2448
        -> coe du_shifted'45'frame_2496 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2450
        -> coe
             du_shifted'45'call'45'closure_2840 (coe v0) (coe v2) (coe v3)
             (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2452 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2454 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2456 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2458 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2464 v6 v7 v8
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2470 v6 v7 v8
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2472 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2474
        -> coe du_shifted'45'save'45'closure_2534 (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2476 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2478 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2480
        -> coe
             seq (coe v5)
             (coe
                du_shifted'45'nz_2922
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_132
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
                      (coe d_floc_86 (coe v4)))
                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Output_58))
                (coe v4) (coe v5))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v6
        -> case coe v6 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v7
               -> coe du_shifted'45'label_2204 (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v7
               -> coe
                    du_shifted'45'jump_2400
                    (coe d_find'45'label_174 (coe v0) (coe v2) (coe v7)) (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v7
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           seq (coe v9)
                           (coe
                              du_shifted'45'test_2878 (coe v0) (coe v7) (coe v2)
                              (coe
                                 du_tag'45'test_118
                                 (coe
                                    d_flat'45'read'45'tag_128 (coe v0) (coe d_falloc_88 (coe v3))
                                    (coe d_floc_86 (coe v3))))
                              (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v7 v8
               -> coe du_shifted'45'thunk_2260 (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v7
               -> coe du_shifted'45'ret_2374 (coe v7) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v7
               -> coe
                    du_shifted'45'call'45'at_2624
                    (coe d_find'45'fn_252 (coe v0) (coe v2) (coe v7)) (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v7
               -> coe du_shifted'45'thunk_2260 (coe v5)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
               -> coe du_shifted'45'leave_2230 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2484 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2486 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2488 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2490 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2492 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2494 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2496 v6
        -> coe du_shifted'45'straight_2142 (coe v1) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr-prog-irrelevant
d_flat'45'exec'45'instr'45'prog'45'irrelevant_3584 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prog'45'irrelevant_3584 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-call-code-prefix
d_do'45'call'45'code'45'prefix_3848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'code'45'prefix_3848 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-call-sv-prefix
d_do'45'call'45'sv'45'prefix_3896 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'sv'45'prefix_3896 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-call-prefix
d_do'45'call'45'prefix_3940 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'call'45'prefix_3940 = erased
-- Once.CCC.Machine.Flat.FlatMachine.test-prefix
d_test'45'prefix_3960 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_test'45'prefix_3960 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr-prefix
d_flat'45'exec'45'instr'45'prefix_3998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flat'45'exec'45'instr'45'prefix_3998 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shift
d_shift_4272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_72 -> T_FlatState_72
d_shift_4272 ~v0 v1 v2 = du_shift_4272 v1 v2
du_shift_4272 :: Integer -> T_FlatState_72 -> T_FlatState_72
du_shift_4272 v0 v1
  = coe
      C_mkFlatFull_98 (coe d_floc_86 (coe v1)) (coe d_falloc_88 (coe v1))
      (coe addInt (coe d_fpc_90 (coe v1)) (coe v0))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe addInt (coe v0))
         (coe d_fret_92 (coe v1)))
      (coe d_fclosure_94 (coe v1))
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64 (addInt (coe v0))
         (d_flink_96 (coe v1)))
-- Once.CCC.Machine.Flat.FlatMachine.shifted-shift
d_shifted'45'shift_4286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shifted'45'shift_4286 ~v0 ~v1 ~v2 = du_shifted'45'shift_4286
du_shifted'45'shift_4286 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shifted'45'shift_4286
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
-- Once.CCC.Machine.Flat.FlatMachine.shifted-eq
d_shifted'45'eq_4298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shifted'45'eq_4298 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-jump
d_flink'45'do'45'jump_4306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_4306 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-branch
d_flink'45'do'45'branch_4320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_4320 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-branch-test
d_flink'45'do'45'branch'45'test_4342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch'45'test_4342 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-nz
d_flink'45'do'45'nz_4362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_62 ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'nz_4362 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-ret
d_flink'45'do'45'ret_4380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [Integer] ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_4380 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.to
d_to_4400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  [Integer] ->
  T_FlatState_72 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to_4400 = erased
-- Once.CCC.Machine.Flat.FlatMachine.FlinkView
d_FlinkView_4404 a0 a1 = ()
data T_FlinkView_4404
  = C_fv'45'call_4408 |
    C_fv'45'call'45'fn_4412 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 |
    C_fv'45'thunk_4418 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
                       Integer |
    C_fv'45'start_4422 Integer | C_fv'45'pres_4428
-- Once.CCC.Machine.Flat.FlatMachine.flinkView
d_flinkView_4432 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlinkView_4404
d_flinkView_4432 ~v0 v1 = du_flinkView_4432 v1
du_flinkView_4432 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  T_FlinkView_4404
du_flinkView_4432 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2420
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2422
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2424
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2426
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2428 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2430 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2432
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2434
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2436 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2438 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2440 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2442 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2444 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2446 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2448
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2450
        -> coe C_fv'45'call_4408
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2452 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2454 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2456 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2458 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2464 v1 v2 v3
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2470 v1 v2 v3
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2472 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2474
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2476 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2478 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2480
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2482 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v2
               -> coe C_fv'45'pres_4428
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v2
               -> coe C_fv'45'pres_4428
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v2
               -> coe C_fv'45'pres_4428
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v2 v3
               -> coe C_fv'45'thunk_4418 v2 v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v2
               -> coe C_fv'45'pres_4428
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v2
               -> coe C_fv'45'call'45'fn_4412 v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v2
               -> coe C_fv'45'start_4422 v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
               -> coe C_fv'45'pres_4428
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2484 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2486 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2488 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2490 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2492 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2494 v1
        -> coe C_fv'45'pres_4428
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2496 v1
        -> coe C_fv'45'pres_4428
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.slot-straight
d_slot'45'straight_4626 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'straight_4626 = erased
-- Once.CCC.Machine.Flat.FlatMachine.slot-gate-ok
d_slot'45'gate'45'ok_4776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'gate'45'ok_4776 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_slot'45'gate'45'ok_4776 v4
du_slot'45'gate'45'ok_4776 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'gate'45'ok_4776 v0 = coe du_slot'45'in_1968 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.slot-go
d_slot'45'go_4798 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'go_4798 = erased
-- Once.CCC.Machine.Flat.FlatMachine.slot-go-ok
d_slot'45'go'45'ok_4818 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'go'45'ok_4818 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.nf′
d_nf'8242'_4834 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nf'8242'_4834 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat
d_exec'45'flat_4840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_exec'45'flat_4840 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_step'45'dispatch_4842 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_278
                   (coe d_floc_86 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.step-dispatch
d_step'45'dispatch_4842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_step'45'dispatch_4842 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else coe
             d_fetch'45'dispatch_4844 v0
             (coe du_fetch_258 (coe v3) (coe d_fpc_90 (coe v4))) v2 v3 v4
-- Once.CCC.Machine.Flat.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_4844 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> T_FlatState_72
d_fetch'45'dispatch_4844 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 v5 ->
                d_exec'45'flat_4840
                  (coe v0) (coe v3) (coe v4)
                  (coe d_flat'45'exec'45'instr_2058 v0 v2 v4 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_98
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_286
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_272
                        (coe d_floc_86 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_274
                        (coe d_floc_86 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_276
                        (coe d_floc_86 (coe v4)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_ev'45'log_280
                        (coe d_floc_86 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_left_282
                        (coe d_floc_86 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_faulted_284
                        (coe d_floc_86 (coe v4))))
                  (coe d_falloc_88 (coe v4)) (coe d_fpc_90 (coe v4))
                  (coe d_fret_92 (coe v4)) (coe d_fclosure_94 (coe v4))
                  (coe d_flink_96 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-reloc
d_exec'45'flat'45'reloc_4890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'flat'45'reloc_4890 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8
  = du_exec'45'flat'45'reloc_4890 v0 v1 v2 v3 v4 v5 v8
du_exec'45'flat'45'reloc_4890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'flat'45'reloc_4890 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      0 -> coe v6
      _ -> let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                seq (coe v6)
                (coe
                   du_reloc'45'step_4912 (coe v0)
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_278
                      (coe d_floc_86 (coe v4)))
                   (coe v7) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)))
-- Once.CCC.Machine.Flat.FlatMachine.reloc-step
d_reloc'45'step_4912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'step_4912 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_reloc'45'step_4912 v0 v1 v2 v3 v4 v5 v6 v9
du_reloc'45'step_4912 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'step_4912 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v1
      then coe v7
      else (case coe v7 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                -> case coe v9 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                       -> coe
                            seq (coe v11)
                            (coe
                               du_reloc'45'fetch_4934 (coe v0)
                               (coe
                                  du_fetch_258
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v4))
                                  (coe d_fpc_90 (coe v5)))
                               (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.Flat.FlatMachine.reloc-fetch
d_reloc'45'fetch_4934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reloc'45'fetch_4934 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_reloc'45'fetch_4934 v0 v1 v2 v3 v4 v5 v6 v9
du_reloc'45'fetch_4934 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_reloc'45'fetch_4934 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             du_exec'45'flat'45'reloc_4890 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe
                d_flat'45'exec'45'instr_2058 v0 v8
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v4))
                v5)
             (coe d_flat'45'exec'45'instr_2058 v0 v8 v4 v6)
             (coe
                du_shifted'45'instr_2984 (coe v0) (coe v8) (coe v4) (coe v5)
                (coe v6) (coe v7))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_shifted'45'halt_2562 (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_5034 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_5034 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_5058 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_5058 = erased
-- Once.CCC.Machine.Flat.FlatMachine.≡ᵇ-true
d_'8801''7495''45'true_5084 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_5084 = erased
-- Once.CCC.Machine.Flat.FlatMachine.lab-eq
d_lab'45'eq_5096 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_5096 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.just-inj
d_just'45'inj_5112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_5112 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-lands
d_fl'45'go'45'lands_5126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_5126 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'lands_5126 v0 v1 v2 v3 v4
du_fl'45'go'45'lands_5126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_5126 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_5178 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_134 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.step
d_step_5154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_5154 v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 ~v8
  = du_step_5154 v0 v2 v3 v4 v7
du_step_5154 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_5154 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_fl'45'go'45'lands_5126 (coe v0) (coe v1) (coe v2)
              (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe addInt (coe (1 :: Integer)) (coe v6))
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v9))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_5178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_5178 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_go_5178 v0 v2 v3 v4 v5 v7
du_go_5178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_5178 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_match_5202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__150 (coe v6)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_step_5154 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._._.match
d_match_5202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_match_5202 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_match_5202 v0 v4 v5 v6 v7 v10
du_match_5202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_match_5202 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      else coe du_step_5154 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Machine.Flat.FlatMachine._._._.just-inj
d_just'45'inj_5216 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_5216 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-lands
d_find'45'label'45'lands_5242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_5242 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_5280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_5280 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightStep
d_StraightStep_5300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 -> ()
d_StraightStep_5300 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_5316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
   T_FlatState_72 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_5316 = erased
-- Once.CCC.Machine.Flat.FlatMachine.Straight
d_Straight_5332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] -> ()
d_Straight_5332 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-All
d_fetch'45'All_5342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_5342 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_fetch'45'All_5342 v2 v3 v5
du_fetch'45'All_5342 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_fetch'45'All_5342 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             0 -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
                      -> coe v7
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v2 of
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v8 v9
                         -> coe du_fetch'45'All_5342 (coe v4) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-Straight
d_fetch'45'Straight_5366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_5366 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_5388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_FlatState_72 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
   T_FlatState_72 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (T_FlatState_72 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2418] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  T_FlatState_72 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_5388 = erased
