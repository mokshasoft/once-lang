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
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Memory.HeapAddress

-- Once.CCC.Machine.Flat.FlatMachine._.exec-trace
d_exec'45'trace_64 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_64 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2808 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState
d_FlatState_68 a0 = ()
data T_FlatState_68
  = C_mkFlatFull_94 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
                    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 Integer
                    [Integer] MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
                    (Maybe Integer)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.floc
d_floc_82 ::
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_floc_82 v0
  = case coe v0 of
      C_mkFlatFull_94 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.falloc
d_falloc_84 ::
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_falloc_84 v0
  = case coe v0 of
      C_mkFlatFull_94 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fpc
d_fpc_86 :: T_FlatState_68 -> Integer
d_fpc_86 v0
  = case coe v0 of
      C_mkFlatFull_94 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fret
d_fret_88 :: T_FlatState_68 -> [Integer]
d_fret_88 v0
  = case coe v0 of
      C_mkFlatFull_94 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fclosure
d_fclosure_90 ::
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_fclosure_90 v0
  = case coe v0 of
      C_mkFlatFull_94 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.flink
d_flink_92 :: T_FlatState_68 -> Maybe Integer
d_flink_92 v0
  = case coe v0 of
      C_mkFlatFull_94 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.mkFlat
d_mkFlat_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> T_FlatState_68
d_mkFlat_96 v0 v1 v2
  = coe
      C_mkFlatFull_94 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72
         (coe (0 :: Integer)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Machine.Flat.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_104 ~v0 v1 = du_sv'45'is'45'zero_104 v1
du_sv'45'is'45'zero_104 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_104 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v2
           -> case coe v2 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.tag-zf
d_tag'45'zf_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_106 ~v0 v1 = du_tag'45'zf_106 v1
du_tag'45'zf_106 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_106 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'is'45'zero_104 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-at
d_flat'45'read'45'at_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_110 ~v0 v1 v2
  = du_flat'45'read'45'at_110 v1 v2
du_flat'45'read'45'at_110 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_110 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_638 (coe v0)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_118 ~v0 v1 = du_flat'45'read'45'tag_118 v1
du_flat'45'read'45'tag_118 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_118 v0
  = coe
      du_flat'45'read'45'at_110 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1354
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
-- Once.CCC.Machine.Flat.FlatMachine.label-of?
d_label'45'of'63'_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_122 ~v0 v1 = du_label'45'of'63'_122 v1
du_label'45'of'63'_122 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_122 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.fl-go
d_fl'45'go_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_126 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_fl'45'at_128 (coe v0) (coe du_label'45'of'63'_122 (coe v4))
             (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-at
d_fl'45'at_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_128 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_fl'45'label'45'match_130 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v5)
                (coe v3))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_fl'45'go_126 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-label-match
d_fl'45'label'45'match_130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_130 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_fl'45'go_126 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-label
d_find'45'label_162 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_162 v0 v1 v2
  = coe
      d_fl'45'go_126 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?
d_thunk'45'of'63'_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_168 ~v0 v1 = du_thunk'45'of'63'_168 v1
du_thunk'45'of'63'_168 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_168 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2208 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.ft-go
d_ft'45'go_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_172 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_ft'45'at_174 (coe v0) (coe du_thunk'45'of'63'_168 (coe v4))
             (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-at
d_ft'45'at_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'at_174 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_ft'45'match_176 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v5)
                (coe v3))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_ft'45'go_172 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-match
d_ft'45'match_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_176 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_ft'45'go_172 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk
d_find'45'thunk_208 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_208 v0 v1 v2
  = coe
      d_ft'45'go_172 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.fetch
d_fetch_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212
d_fetch_214 ~v0 v1 v2 = du_fetch_214 v1 v2
du_fetch_214 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212
du_fetch_214 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_fetch_214 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.just-injℕ
d_just'45'injℕ_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_226 = erased
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?-sound
d_thunk'45'of'63''45'sound_234 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_234 ~v0 v1 ~v2 ~v3
  = du_thunk'45'of'63''45'sound_234 v1
du_thunk'45'of'63''45'sound_234 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_234 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2208 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-go-sound
d_ft'45'go'45'sound_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_254 v0 v1 v2 v3 v4 ~v5
  = du_ft'45'go'45'sound_254 v0 v1 v2 v3 v4
du_ft'45'go'45'sound_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_254 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_284 (coe v0) (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_thunk'45'of'63'_168 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_284 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_go_284 v0 v1 v2 v3 v4 v5 v7
du_go_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_284 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_go'45'm_294 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v7)
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_ft'45'go'45'sound_254 (coe v0) (coe v2) (coe v3)
                      (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_ft'45'go'45'sound_254 (coe v0) (coe v2) (coe v3)
                         (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-m
d_go'45'm_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'm_294 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go'45'm_294 v0 v1 v2 v3 v4 v5 v8
du_go'45'm_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'm_294 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe du_ts_306 (coe v1)))
                   erased))
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_ft'45'go'45'sound_254 (coe v0) (coe v2) (coe v3)
                      (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_ft'45'go'45'sound_254 (coe v0) (coe v2) (coe v3)
                         (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)))))
-- Once.CCC.Machine.Flat.FlatMachine._._.ts
d_ts_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ts_306 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_ts_306 v1
du_ts_306 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ts_306 v0 = coe du_thunk'45'of'63''45'sound_234 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine._._.acc≡j
d_acc'8801'j_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_308 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.j≡
d_j'8801'_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'_314 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.fe
d_fe_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_316 = erased
-- Once.CCC.Machine.Flat.FlatMachine.label-of?-sound
d_label'45'of'63''45'sound_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_346 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-sound
d_fl'45'go'45'sound_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_362 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'sound_362 v0 v1 v2 v3 v4
du_fl'45'go'45'sound_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_362 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_390 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_122 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_390 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_go_390 v0 v2 v3 v4 v5 v7
du_go_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_390 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_go'45'm_398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v6)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_fl'45'go'45'sound_362 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_fl'45'go'45'sound_362 (coe v0) (coe v1) (coe v2)
                         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-m
d_go'45'm_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'm_398 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go'45'm_398 v0 v2 v3 v4 v5 v8
du_go'45'm_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'm_398 v0 v1 v2 v3 v4 v5
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
                      du_fl'45'go'45'sound_362 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_fl'45'go'45'sound_362 (coe v0) (coe v1) (coe v2)
                         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))))
-- Once.CCC.Machine.Flat.FlatMachine._._.acc≡j
d_acc'8801'j_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_410 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.j≡
d_j'8801'_416 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'_416 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.fe
d_fe_418 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_418 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-sound
d_find'45'label'45'sound_450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_450 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.r
d_r_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_464 v0 v1 v2 v3 ~v4 = du_r_464 v0 v1 v2 v3
du_r_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_r_464 v0 v1 v2 v3
  = coe
      du_fl'45'go'45'sound_362 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine._.d
d_d_466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_d_466 v0 v1 v2 v3 ~v4 = du_d_466 v0 v1 v2 v3
du_d_466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_d_466 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_r_464 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine._.j≡d
d_j'8801'd_468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'd_468 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.fe
d_fe_470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_470 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk-sound
d_find'45'thunk'45'sound_482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_482 v0 v1 v2 v3 ~v4
  = du_find'45'thunk'45'sound_482 v0 v1 v2 v3
du_find'45'thunk'45'sound_482 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_482 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_b_502 (coe v0) (coe v1) (coe v2) (coe v3)) erased
-- Once.CCC.Machine.Flat.FlatMachine._.r
d_r_496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_496 v0 v1 v2 v3 ~v4 = du_r_496 v0 v1 v2 v3
du_r_496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_r_496 v0 v1 v2 v3
  = coe
      du_ft'45'go'45'sound_254 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine._.d
d_d_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_d_498 v0 v1 v2 v3 ~v4 = du_d_498 v0 v1 v2 v3
du_d_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_d_498 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_r_496 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine._.j≡d
d_j'8801'd_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'd_500 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.b
d_b_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_b_502 v0 v1 v2 v3 ~v4 = du_b_502 v0 v1 v2 v3
du_b_502 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_b_502 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_r_496 (coe v0) (coe v1) (coe v2) (coe v3))))
-- Once.CCC.Machine.Flat.FlatMachine._.fe
d_fe_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_504 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-jump
d_do'45'jump_508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_68 -> T_FlatState_68
d_do'45'jump_508 ~v0 v1 = du_do'45'jump_508 v1
du_do'45'jump_508 ::
  Maybe Integer -> T_FlatState_68 -> T_FlatState_68
du_do'45'jump_508 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  C_mkFlatFull_94 (coe d_floc_82 (coe v2)) (coe d_falloc_84 (coe v2))
                  (coe v1) (coe d_fret_88 (coe v2)) (coe d_fclosure_90 (coe v2))
                  (coe d_flink_92 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_94
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                        (coe d_floc_82 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
                        (coe d_floc_82 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
                        (coe d_floc_82 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_84 (coe v1)) (coe d_fpc_86 (coe v1))
                  (coe d_fret_88 (coe v1)) (coe d_fclosure_90 (coe v1))
                  (coe d_flink_92 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-branch
d_do'45'branch_516 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'branch_516 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 ->
                coe
                  du_do'45'jump_508 (d_find'45'label_162 (coe v0) (coe v3) (coe v2))
                  v4)
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_94 (coe d_floc_82 (coe v4)) (coe d_falloc_84 (coe v4))
                  (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v4)))
                  (coe d_fret_88 (coe v4)) (coe d_fclosure_90 (coe v4))
                  (coe d_flink_92 (coe v4)))
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'step'45'straight_526 v0 v1 v2
  = coe
      C_mkFlatFull_94
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2806
            (coe v0) (coe v1) (coe d_floc_82 (coe v2))
            (coe d_falloc_84 (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2806
            (coe v0) (coe v1) (coe d_floc_82 (coe v2))
            (coe d_falloc_84 (coe v2))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v2)))
      (coe d_fret_88 (coe v2)) (coe d_fclosure_90 (coe v2))
      (coe d_flink_92 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.enter-frame
d_enter'45'frame_532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'frame_532 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_104 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
               (coe v2))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576
               (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v2)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.enter-call
d_enter'45'call_538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_enter'45'call_538 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_104 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v1))
         (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
               (coe v1))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_576
               (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
            (coe v1)))
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v1))
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame'45'aux_542 ~v0 v1
  = du_leave'45'frame'45'aux_542 v1
du_leave'45'frame'45'aux_542 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame'45'aux_542 v0
  = case coe v0 of
      [] -> coe (\ v1 -> v1)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    (\ v5 ->
                       coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584 (coe v3)
                         (coe v2) (coe v4)
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v5))
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
                            (coe v5))
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame
d_leave'45'frame_554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_leave'45'frame_554 ~v0 v1 = du_leave'45'frame_554 v1
du_leave'45'frame_554 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
du_leave'45'frame_554 v0
  = coe
      du_leave'45'frame'45'aux_542
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v0))
      v0
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_560 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_560 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_578 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_578 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_596 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_608 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_608 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_624 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_absurd_624
du_absurd_624 :: AgdaAny
du_absurd_624 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_634 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_652 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_662 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_662 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_672 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_672 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_682 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_682 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_692 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_692 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_702 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_702 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_710 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488) ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'step'45'frame_710 v0 v1 v2 v3
  = coe
      C_mkFlatFull_94
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2806
            (coe v0) (coe v1) (coe d_floc_82 (coe v3))
            (coe d_falloc_84 (coe v3))))
      (coe
         v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2806
               (coe v0) (coe v1) (coe d_floc_82 (coe v3))
               (coe d_falloc_84 (coe v3)))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v3)))
      (coe d_fret_88 (coe v3)) (coe d_fclosure_90 (coe v3))
      (coe d_flink_92 (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.do-ret
d_do'45'ret_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] -> T_FlatState_68 -> T_FlatState_68
d_do'45'ret_718 ~v0 v1 = du_do'45'ret_718 v1
du_do'45'ret_718 :: [Integer] -> T_FlatState_68 -> T_FlatState_68
du_do'45'ret_718 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_94
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                        (coe d_floc_82 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
                        (coe d_floc_82 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
                        (coe d_floc_82 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe du_leave'45'frame_554 (coe d_falloc_84 (coe v1)))
                  (coe d_fpc_86 (coe v1)) (coe d_fret_88 (coe v1))
                  (coe d_fclosure_90 (coe v1)) (coe d_flink_92 (coe v1)))
      (:) v1 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkFlatFull_94 (coe d_floc_82 (coe v3))
                  (coe du_leave'45'frame_554 (coe d_falloc_84 (coe v3))) (coe v1)
                  (coe v2) (coe d_fclosure_90 (coe v3)) (coe d_flink_92 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_730 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_730 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_742 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_742 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_756 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_absurd_756
du_absurd_756 :: AgdaAny
du_absurd_756 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_764 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_764 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_780 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_780 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_792 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_792 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_806 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_absurd_806
du_absurd_806 :: AgdaAny
du_absurd_806 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_814 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_814 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-alloc
d_do'45'ret'45'alloc_830 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_830 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_840 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_840 = erased
-- Once.CCC.Machine.Flat.FlatMachine.grow-frame
d_grow'45'frame_846 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488
d_grow'45'frame_846 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_584
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_104 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_574
         (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_578 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_580
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_582 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.do-thunk
d_do'45'thunk_852 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_68 -> T_FlatState_68
d_do'45'thunk_852 v0 v1 v2
  = coe
      C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
            (coe d_floc_82 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_clear'45'frame_694 (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
               (coe d_floc_82 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_104 v0
               (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_572
                  (coe d_falloc_84 (coe v2)))
               v1)
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe d_floc_82 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
            (coe d_floc_82 (coe v2))))
      (coe
         d_grow'45'frame_846 (coe v0) (coe v1) (coe d_falloc_84 (coe v2)))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v2)))
      (coe d_fret_88 (coe v2)) (coe d_fclosure_90 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Once.CCC.Machine.Flat.FlatMachine.flat-halt
d_flat'45'halt_858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'halt_858 ~v0 v1 = du_flat'45'halt_858 v1
du_flat'45'halt_858 :: T_FlatState_68 -> T_FlatState_68
du_flat'45'halt_858 v0
  = coe
      C_mkFlatFull_94
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
            (coe d_floc_82 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
            (coe d_floc_82 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
            (coe d_floc_82 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      (coe d_falloc_84 (coe v0)) (coe d_fpc_86 (coe v0))
      (coe d_fret_88 (coe v0)) (coe d_fclosure_90 (coe v0))
      (coe d_flink_92 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.do-call-at
d_do'45'call'45'at_862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_68 -> T_FlatState_68
d_do'45'call'45'at_862 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkFlatFull_94 (coe d_floc_82 (coe v3))
                  (coe d_enter'45'call_538 (coe v0) (coe d_falloc_84 (coe v3)))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v3)))
                     (coe d_fret_88 (coe v3)))
                  (coe d_fclosure_90 (coe v3))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v3)))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe du_flat'45'halt_858 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call-code
d_do'45'call'45'code_870 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'call'45'code_870 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v5
               -> coe du_flat'45'halt_858 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v5
               -> coe du_flat'45'halt_858 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v5 v6 v7
               -> coe du_flat'45'halt_858 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v5
               -> coe
                    d_do'45'call'45'at_862 v0
                    (d_find'45'thunk_208 (coe v0) (coe v1) (coe v5)) v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_flat'45'halt_858 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call-sv
d_do'45'call'45'sv_894 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'call'45'sv_894 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe du_flat'45'halt_858 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    d_do'45'call'45'code_870 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
                       (d_floc_82 (coe v3))
                       (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v5)))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v4
        -> coe du_flat'45'halt_858 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v4 v5 v6
        -> coe du_flat'45'halt_858 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v4
        -> coe du_flat'45'halt_858 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call
d_do'45'call_918 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'call_918 v0 v1 v2
  = coe
      d_do'45'call'45'sv_894 (coe v0) (coe v1)
      (coe d_fclosure_90 (coe v2)) (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.CallPost
d_CallPost_928 a0 a1 a2 = ()
data T_CallPost_928
  = C_cp'45'halt_934 |
    C_cp'45'enter_940 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 Integer
-- Once.CCC.Machine.Flat.FlatMachine.callView
d_callView_946 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_CallPost_928
d_callView_946 v0 v1 v2
  = coe
      du_go'45'sv_1054 (coe v0) (coe v1) (coe v2)
      (coe d_fclosure_90 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine._.go-at
d_go'45'at_962 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_928
d_go'45'at_962 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_go'45'at_962 v3 v5
du_go'45'at_962 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_CallPost_928
du_go'45'at_962 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_cp'45'enter_940 v1 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_cp'45'halt_934
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-code
d_go'45'code_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_928
d_go'45'code_1002 v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_go'45'code_1002 v0 v1 v3
du_go'45'code_1002 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_CallPost_928
du_go'45'code_1002 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v4
               -> coe C_cp'45'halt_934
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v4
               -> coe C_cp'45'halt_934
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v4 v5 v6
               -> coe C_cp'45'halt_934
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v4
               -> coe
                    du_go'45'at_962
                    (coe d_find'45'thunk_208 (coe v0) (coe v1) (coe v4)) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_cp'45'halt_934
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-sv
d_go'45'sv_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_928
d_go'45'sv_1054 v0 v1 v2 v3 ~v4 = du_go'45'sv_1054 v0 v1 v2 v3
du_go'45'sv_1054 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  T_CallPost_928
du_go'45'sv_1054 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_70 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe C_cp'45'halt_934
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_go'45'code_1002 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
                       (d_floc_82 (coe v2))
                       (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v4
        -> coe C_cp'45'halt_934
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76 v4 v5 v6
        -> coe C_cp'45'halt_934
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_78 v4
        -> coe C_cp'45'halt_934
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-save-closure
d_do'45'save'45'closure_1076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'save'45'closure_1076 ~v0 v1
  = du_do'45'save'45'closure_1076 v1
du_do'45'save'45'closure_1076 :: T_FlatState_68 -> T_FlatState_68
du_do'45'save'45'closure_1076 v0
  = coe
      C_mkFlatFull_94 (coe d_floc_82 (coe v0)) (coe d_falloc_84 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v0)))
      (coe d_fret_88 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
            (coe d_floc_82 (coe v0)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
      (coe d_flink_92 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_1080 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'exec'45'instr_1080 v0 v1
  = let v2
          = \ v2 v3 ->
              d_flat'45'step'45'straight_526 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2234 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_710
                     (coe v0) (coe v1) (coe d_enter'45'frame_532 (coe v0) (coe v3))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2236 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_710
                     (coe v0) (coe v1) (coe du_leave'45'frame_554) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2240 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_710
                     (coe v0) (coe v1)
                     (coe
                        d_enter'45'frame_532 (coe v0)
                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2242
           -> coe
                (\ v3 v4 ->
                   d_flat'45'step'45'frame_710
                     (coe v0) (coe v1) (coe du_leave'45'frame_554) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244
           -> coe (\ v3 v4 -> d_do'45'call_918 (coe v0) (coe v3) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268
           -> coe (\ v3 v4 -> coe du_do'45'save'45'closure_1076 (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            C_mkFlatFull_94 (coe d_floc_82 (coe v6)) (coe d_falloc_84 (coe v6))
                            (coe addInt (coe (1 :: Integer)) (coe d_fpc_86 (coe v6)))
                            (coe d_fret_88 (coe v6)) (coe d_fclosure_90 (coe v6))
                            (coe d_flink_92 (coe v6)))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            du_do'45'jump_508 (d_find'45'label_162 (coe v0) (coe v5) (coe v4))
                            v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_516 v0
                            (coe
                               du_sv'45'is'45'zero_104
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_148
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                                     (coe d_floc_82 (coe v6)))
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_60)))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_516 v0
                            (coe
                               du_tag'45'zf_106
                               (coe du_flat'45'read'45'tag_118 (coe d_floc_82 (coe v6))))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2208 v4 v5
                  -> coe (\ v6 v7 -> d_do'45'thunk_852 (coe v0) (coe v5) (coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2210 v4
                  -> coe (\ v5 v6 -> coe du_do'45'ret_718 (d_fret_88 (coe v6)) v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-jump
d_flink'45'do'45'jump_1138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'jump_1138 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-branch
d_flink'45'do'45'branch_1152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'branch_1152 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flink-do-ret
d_flink'45'do'45'ret_1170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flink'45'do'45'ret_1170 = erased
-- Once.CCC.Machine.Flat.FlatMachine.FlinkView
d_FlinkView_1178 a0 a1 = ()
data T_FlinkView_1178
  = C_fv'45'call_1182 |
    C_fv'45'thunk_1188 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                       Integer |
    C_fv'45'pres_1194
-- Once.CCC.Machine.Flat.FlatMachine.flinkView
d_flinkView_1198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_FlinkView_1178
d_flinkView_1198 ~v0 v1 = du_flinkView_1198 v1
du_flinkView_1198 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  T_FlinkView_1178
du_flinkView_1198 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2214
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2216
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2218
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2220
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2222 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2224 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2226
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2228
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2230 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2232 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2234 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2236 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2238 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2240 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2242
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2244
        -> coe C_fv'45'call_1182
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2246 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2248 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2250 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2252 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2258 v1 v2 v3
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2264 v1 v2 v3
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2266 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2268
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2270 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2272 v1 v2
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2274 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2276 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2278 v1
        -> coe C_fv'45'pres_1194
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2280 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2200 v2
               -> coe C_fv'45'pres_1194
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2202 v2
               -> coe C_fv'45'pres_1194
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2204 v2
               -> coe C_fv'45'pres_1194
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2206 v2
               -> coe C_fv'45'pres_1194
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2208 v2 v3
               -> coe C_fv'45'thunk_1188 v2 v3
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2210 v2
               -> coe C_fv'45'pres_1194
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2282 v1
        -> coe C_fv'45'pres_1194
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat
d_exec'45'flat_1348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_FlatState_68
d_exec'45'flat_1348 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_step'45'dispatch_1350 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420
                   (coe d_floc_82 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.step-dispatch
d_step'45'dispatch_1350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_FlatState_68
d_step'45'dispatch_1350 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else coe
             d_fetch'45'dispatch_1352 v0
             (coe du_fetch_214 (coe v3) (coe d_fpc_86 (coe v4))) v2 v3 v4
-- Once.CCC.Machine.Flat.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_1352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> T_FlatState_68
d_fetch'45'dispatch_1352 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 v5 ->
                d_exec'45'flat_1348
                  (coe v0) (coe v3) (coe v4)
                  (coe d_flat'45'exec'45'instr_1080 v0 v2 v4 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_94
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414
                        (coe d_floc_82 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416
                        (coe d_floc_82 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418
                        (coe d_floc_82 (coe v4)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_84 (coe v4)) (coe d_fpc_86 (coe v4))
                  (coe d_fret_88 (coe v4)) (coe d_fclosure_90 (coe v4))
                  (coe d_flink_92 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_1386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_1386 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_1410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_1410 = erased
-- Once.CCC.Machine.Flat.FlatMachine.≡ᵇ-true
d_'8801''7495''45'true_1436 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_1436 = erased
-- Once.CCC.Machine.Flat.FlatMachine.lab-eq
d_lab'45'eq_1448 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_1448 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.just-inj
d_just'45'inj_1464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_1464 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-lands
d_fl'45'go'45'lands_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_1478 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'lands_1478 v0 v1 v2 v3 v4
du_fl'45'go'45'lands_1478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_1478 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_1530 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_122 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.step
d_step_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_1506 v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 ~v8
  = du_step_1506 v0 v2 v3 v4 v7
du_step_1506 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_1506 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_fl'45'go'45'lands_1478 (coe v0) (coe v1) (coe v2)
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
d_go_1530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1530 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_go_1530 v0 v2 v3 v4 v5 v7
du_go_1530 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1530 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_match_1554 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v6)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_step_1506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._._.match
d_match_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_match_1554 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_match_1554 v0 v4 v5 v6 v7 v10
du_match_1554 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_match_1554 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      else coe du_step_1506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Machine.Flat.FlatMachine._._._.just-inj
d_just'45'inj_1568 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_1568 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-lands
d_find'45'label'45'lands_1594 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_1594 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_1632 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_1632 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightStep
d_StraightStep_1652 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 -> ()
d_StraightStep_1652 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_1668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
   T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_1668 = erased
-- Once.CCC.Machine.Flat.FlatMachine.Straight
d_Straight_1684 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] -> ()
d_Straight_1684 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-All
d_fetch'45'All_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_1694 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_fetch'45'All_1694 v2 v3 v5
du_fetch'45'All_1694 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_fetch'45'All_1694 v0 v1 v2
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
                         -> coe du_fetch'45'All_1694 (coe v4) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-Straight
d_fetch'45'Straight_1718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_1718 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_1740 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
   T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_1740 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shift-loc
d_shift'45'loc_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_1860 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_shift'45'loc_1860 v0 v1 v3 v4 v5 v6
du_shift'45'loc_1860 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_1860 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v7
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v3) in
              coe
                (if coe v7
                   then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                   else (let v8 = coe du_fetch_214 (coe v2) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     du_shift'45'loc_1860 (coe v0) (coe v6) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2806
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2806
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe addInt (coe (1 :: Integer)) (coe v5))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_1988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_1988 = erased
-- Once.CCC.Machine.Flat.FlatMachine.forced
d_forced_2008 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
d_forced_2008 ~v0 v1 = du_forced_2008 v1
du_forced_2008 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402
du_forced_2008 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_422
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_414 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_416 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_418 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_2018 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_2018 ~v0 v1 v2 ~v3 v4
  = du_exec'45'trace'45'is'45'flat_2018 v1 v2 v4
du_exec'45'trace'45'is'45'flat_2018 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2212] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_2018 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_420 (coe v1) in
    coe
      (if coe v3
         then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
         else (case coe v0 of
                 [] -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                 (:) v4 v5
                   -> coe
                        seq (coe v2)
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                 _ -> MAlonzo.RTE.mazUnreachableError))
