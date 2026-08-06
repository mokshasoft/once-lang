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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_64 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2872 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState
d_FlatState_68 a0 = ()
data T_FlatState_68
  = C_mkFlatFull_90 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
                    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 Integer
                    [Integer] MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.floc
d_floc_80 ::
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_80 v0
  = case coe v0 of
      C_mkFlatFull_90 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.falloc
d_falloc_82 ::
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_82 v0
  = case coe v0 of
      C_mkFlatFull_90 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fpc
d_fpc_84 :: T_FlatState_68 -> Integer
d_fpc_84 v0
  = case coe v0 of
      C_mkFlatFull_90 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fret
d_fret_86 :: T_FlatState_68 -> [Integer]
d_fret_86 v0
  = case coe v0 of
      C_mkFlatFull_90 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fclosure
d_fclosure_88 ::
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_88 v0
  = case coe v0 of
      C_mkFlatFull_90 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.mkFlat
d_mkFlat_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> T_FlatState_68
d_mkFlat_92 v0 v1 v2
  = coe
      C_mkFlatFull_90 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Flat.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_100 ~v0 v1 = du_sv'45'is'45'zero_100 v1
du_sv'45'is'45'zero_100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_100 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v2
           -> case coe v2 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.tag-zf
d_tag'45'zf_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_tag'45'zf_102 ~v0 v1 = du_tag'45'zf_102 v1
du_tag'45'zf_102 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_tag'45'zf_102 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'is'45'zero_100 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-at
d_flat'45'read'45'at_106 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'at_106 ~v0 v1 v2
  = du_flat'45'read'45'at_106 v1 v2
du_flat'45'read'45'at_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'at_106 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'tag_114 ~v0 v1 = du_flat'45'read'45'tag_114 v1
du_flat'45'read'45'tag_114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'tag_114 v0
  = coe
      du_flat'45'read'45'at_106 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1428
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
-- Once.CCC.Machine.Flat.FlatMachine.label-of?
d_label'45'of'63'_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_label'45'of'63'_118 ~v0 v1 = du_label'45'of'63'_118 v1
du_label'45'of'63'_118 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_label'45'of'63'_118 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.fl-go
d_fl'45'go_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_122 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_fl'45'at_124 (coe v0) (coe du_label'45'of'63'_118 (coe v4))
             (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-at
d_fl'45'at_124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'at_124 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_fl'45'label'45'match_126 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v5)
                (coe v3))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_fl'45'go_122 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-label-match
d_fl'45'label'45'match_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_126 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_fl'45'go_122 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-label
d_find'45'label_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'label_158 v0 v1 v2
  = coe
      d_fl'45'go_122 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?
d_thunk'45'of'63'_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
d_thunk'45'of'63'_164 ~v0 v1 = du_thunk'45'of'63'_164 v1
du_thunk'45'of'63'_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6
du_thunk'45'of'63'_164 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.ft-go
d_ft'45'go_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_168 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_ft'45'at_170 (coe v0) (coe du_thunk'45'of'63'_164 (coe v4))
             (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-at
d_ft'45'at_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'at_170 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             d_ft'45'match_172 (coe v0)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v5)
                (coe v3))
             (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_ft'45'go_168 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-match
d_ft'45'match_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_172 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_ft'45'go_168 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk
d_find'45'thunk_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_204 v0 v1 v2
  = coe
      d_ft'45'go_168 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.fetch
d_fetch_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
d_fetch_210 ~v0 v1 v2 = du_fetch_210 v1 v2
du_fetch_210 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286
du_fetch_210 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_fetch_210 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.just-injℕ
d_just'45'injℕ_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injℕ_222 = erased
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?-sound
d_thunk'45'of'63''45'sound_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thunk'45'of'63''45'sound_230 ~v0 v1 ~v2 ~v3
  = du_thunk'45'of'63''45'sound_230 v1
du_thunk'45'of'63''45'sound_230 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thunk'45'of'63''45'sound_230 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v2 v3
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-go-sound
d_ft'45'go'45'sound_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ft'45'go'45'sound_250 v0 v1 v2 v3 v4 ~v5
  = du_ft'45'go'45'sound_250 v0 v1 v2 v3 v4
du_ft'45'go'45'sound_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ft'45'go'45'sound_250 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_280 (coe v0) (coe v5) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_thunk'45'of'63'_164 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_280 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_go_280 v0 v1 v2 v3 v4 v5 v7
du_go_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_280 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             du_go'45'm_290 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                      du_ft'45'go'45'sound_250 (coe v0) (coe v2) (coe v3)
                      (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_ft'45'go'45'sound_250 (coe v0) (coe v2) (coe v3)
                         (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-m
d_go'45'm_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'm_290 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go'45'm_290 v0 v1 v2 v3 v4 v5 v8
du_go'45'm_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'm_290 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe du_ts_302 (coe v1)))
                   erased))
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_ft'45'go'45'sound_250 (coe v0) (coe v2) (coe v3)
                      (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_ft'45'go'45'sound_250 (coe v0) (coe v2) (coe v3)
                         (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5)))))
-- Once.CCC.Machine.Flat.FlatMachine._._.ts
d_ts_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ts_302 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_ts_302 v1
du_ts_302 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ts_302 v0 = coe du_thunk'45'of'63''45'sound_230 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine._._.acc≡j
d_acc'8801'j_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_304 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.j≡
d_j'8801'_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'_310 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.fe
d_fe_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_312 = erased
-- Once.CCC.Machine.Flat.FlatMachine.label-of?-sound
d_label'45'of'63''45'sound_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'of'63''45'sound_342 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-sound
d_fl'45'go'45'sound_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'sound_358 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'sound_358 v0 v1 v2 v3 v4
du_fl'45'go'45'sound_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'sound_358 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_386 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_118 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_386 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8
  = du_go_386 v0 v2 v3 v4 v5 v7
du_go_386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_386 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_go'45'm_394 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                      du_fl'45'go'45'sound_358 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_fl'45'go'45'sound_358 (coe v0) (coe v1) (coe v2)
                         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-m
d_go'45'm_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go'45'm_394 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go'45'm_394 v0 v2 v3 v4 v5 v8
du_go'45'm_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go'45'm_394 v0 v1 v2 v3 v4 v5
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
                      du_fl'45'go'45'sound_358 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_fl'45'go'45'sound_358 (coe v0) (coe v1) (coe v2)
                         (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v4)))))
-- Once.CCC.Machine.Flat.FlatMachine._._.acc≡j
d_acc'8801'j_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_406 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.j≡
d_j'8801'_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'_412 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.fe
d_fe_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_414 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-sound
d_find'45'label'45'sound_446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'sound_446 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.r
d_r_460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_460 v0 v1 v2 v3 ~v4 = du_r_460 v0 v1 v2 v3
du_r_460 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_r_460 v0 v1 v2 v3
  = coe
      du_fl'45'go'45'sound_358 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine._.d
d_d_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_d_462 v0 v1 v2 v3 ~v4 = du_d_462 v0 v1 v2 v3
du_d_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_d_462 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_r_460 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine._.j≡d
d_j'8801'd_464 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'd_464 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.fe
d_fe_466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_466 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk-sound
d_find'45'thunk'45'sound_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'sound_478 v0 v1 v2 v3 ~v4
  = du_find'45'thunk'45'sound_478 v0 v1 v2 v3
du_find'45'thunk'45'sound_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'sound_478 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_b_498 (coe v0) (coe v1) (coe v2) (coe v3)) erased
-- Once.CCC.Machine.Flat.FlatMachine._.r
d_r_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r_492 v0 v1 v2 v3 ~v4 = du_r_492 v0 v1 v2 v3
du_r_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_r_492 v0 v1 v2 v3
  = coe
      du_ft'45'go'45'sound_250 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe v3)
-- Once.CCC.Machine.Flat.FlatMachine._.d
d_d_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_d_494 v0 v1 v2 v3 ~v4 = du_d_494 v0 v1 v2 v3
du_d_494 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_d_494 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_r_492 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine._.j≡d
d_j'8801'd_496 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_j'8801'd_496 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.b
d_b_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_b_498 v0 v1 v2 v3 ~v4 = du_b_498 v0 v1 v2 v3
du_b_498 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Integer
du_b_498 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe du_r_492 (coe v0) (coe v1) (coe v2) (coe v3))))
-- Once.CCC.Machine.Flat.FlatMachine._.fe
d_fe_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_500 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-jump
d_do'45'jump_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_68 -> T_FlatState_68
d_do'45'jump_504 ~v0 v1 = du_do'45'jump_504 v1
du_do'45'jump_504 ::
  Maybe Integer -> T_FlatState_68 -> T_FlatState_68
du_do'45'jump_504 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  C_mkFlatFull_90 (coe d_floc_80 (coe v2)) (coe d_falloc_82 (coe v2))
                  (coe v1) (coe d_fret_86 (coe v2)) (coe d_fclosure_88 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_90
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                        (coe d_floc_80 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                        (coe d_floc_80 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                        (coe d_floc_80 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_82 (coe v1)) (coe d_fpc_84 (coe v1))
                  (coe d_fret_86 (coe v1)) (coe d_fclosure_88 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-branch
d_do'45'branch_512 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'branch_512 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 ->
                coe
                  du_do'45'jump_504 (d_find'45'label_158 (coe v0) (coe v3) (coe v2))
                  v4)
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_90 (coe d_floc_80 (coe v4)) (coe d_falloc_82 (coe v4))
                  (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v4)))
                  (coe d_fret_86 (coe v4)) (coe d_fclosure_88 (coe v4)))
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'step'45'straight_522 v0 v1 v2
  = coe
      C_mkFlatFull_90
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
            (coe v0) (coe v1) (coe d_floc_80 (coe v2))
            (coe d_falloc_82 (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
            (coe v0) (coe v1) (coe d_floc_80 (coe v2))
            (coe d_falloc_82 (coe v2))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v2)))
      (coe d_fret_86 (coe v2)) (coe d_fclosure_88 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.enter-frame
d_enter'45'frame_528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_enter'45'frame_528 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
               (coe v2))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
               (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v2)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.enter-call
d_enter'45'call_534 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_enter'45'call_534 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v1))
         (1 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
               (coe v1))
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_frame'45'slots_652
               (coe v1)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
            (coe v1)))
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v1))
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_538 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame'45'aux_538 ~v0 v1
  = du_leave'45'frame'45'aux_538 v1
du_leave'45'frame'45'aux_538 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame'45'aux_538 v0
  = case coe v0 of
      [] -> coe (\ v1 -> v1)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    (\ v5 ->
                       coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660 (coe v3)
                         (coe v2) (coe v4)
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v5))
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
                            (coe v5))
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame
d_leave'45'frame_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame_550 ~v0 v1 = du_leave'45'frame_550 v1
du_leave'45'frame_550 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame_550 v0
  = coe
      du_leave'45'frame'45'aux_538
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      v0
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_556 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_574 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_574 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_592 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_592 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_604 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_604 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_absurd_620
du_absurd_620 :: AgdaAny
du_absurd_620 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_630 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_630 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_648 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_658 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_658 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_668 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_668 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_678 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_678 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_688 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_688 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_698 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_698 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568) ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'step'45'frame_706 v0 v1 v2 v3
  = coe
      C_mkFlatFull_90
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
            (coe v0) (coe v1) (coe d_floc_80 (coe v3))
            (coe d_falloc_82 (coe v3))))
      (coe
         v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
               (coe v0) (coe v1) (coe d_floc_80 (coe v3))
               (coe d_falloc_82 (coe v3)))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v3)))
      (coe d_fret_86 (coe v3)) (coe d_fclosure_88 (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.do-ret
d_do'45'ret_714 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] -> T_FlatState_68 -> T_FlatState_68
d_do'45'ret_714 ~v0 v1 = du_do'45'ret_714 v1
du_do'45'ret_714 :: [Integer] -> T_FlatState_68 -> T_FlatState_68
du_do'45'ret_714 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_90
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                        (coe d_floc_80 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                        (coe d_floc_80 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                        (coe d_floc_80 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe du_leave'45'frame_550 (coe d_falloc_82 (coe v1)))
                  (coe d_fpc_84 (coe v1)) (coe d_fret_86 (coe v1))
                  (coe d_fclosure_88 (coe v1)))
      (:) v1 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkFlatFull_90 (coe d_floc_80 (coe v3))
                  (coe du_leave'45'frame_550 (coe d_falloc_82 (coe v3))) (coe v1)
                  (coe v2) (coe d_fclosure_88 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_726 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_726 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_738 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_738 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_752 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_absurd_752
du_absurd_752 :: AgdaAny
du_absurd_752 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_760 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_760 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_776 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_788 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_788 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_802 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_absurd_802
du_absurd_802 :: AgdaAny
du_absurd_802 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_810 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_810 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-alloc
d_do'45'ret'45'alloc_826 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_826 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_836 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_836 = erased
-- Once.CCC.Machine.Flat.FlatMachine.grow-frame
d_grow'45'frame_842 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_grow'45'frame_842 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_660
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_654 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_656
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_658 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.do-thunk
d_do'45'thunk_848 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_68 -> T_FlatState_68
d_do'45'thunk_848 v0 v1 v2
  = coe
      C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe d_floc_80 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_clear'45'frame_768 (coe v0)
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
               (coe d_floc_80 (coe v2)))
            (coe
               MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
               (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_648
                  (coe d_falloc_82 (coe v2)))
               v1)
            (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe d_floc_80 (coe v2)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
            (coe d_floc_80 (coe v2))))
      (coe
         d_grow'45'frame_842 (coe v0) (coe v1) (coe d_falloc_82 (coe v2)))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v2)))
      (coe d_fret_86 (coe v2)) (coe d_fclosure_88 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.flat-halt
d_flat'45'halt_854 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'halt_854 ~v0 v1 = du_flat'45'halt_854 v1
du_flat'45'halt_854 :: T_FlatState_68 -> T_FlatState_68
du_flat'45'halt_854 v0
  = coe
      C_mkFlatFull_90
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe d_floc_80 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
            (coe d_floc_80 (coe v0)))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
            (coe d_floc_80 (coe v0)))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      (coe d_falloc_82 (coe v0)) (coe d_fpc_84 (coe v0))
      (coe d_fret_86 (coe v0)) (coe d_fclosure_88 (coe v0))
-- Once.CCC.Machine.Flat.FlatMachine.do-call-at
d_do'45'call'45'at_858 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_68 -> T_FlatState_68
d_do'45'call'45'at_858 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkFlatFull_90 (coe d_floc_80 (coe v3))
                  (coe d_enter'45'call_534 (coe v0) (coe d_falloc_82 (coe v3)))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v3)))
                     (coe d_fret_86 (coe v3)))
                  (coe d_fclosure_88 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe (\ v2 -> coe du_flat'45'halt_854 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call-code
d_do'45'call'45'code_866 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'call'45'code_866 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v5
               -> coe du_flat'45'halt_854 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v5
               -> coe du_flat'45'halt_854 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v5 v6 v7
               -> coe du_flat'45'halt_854 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v5
               -> coe
                    d_do'45'call'45'at_858 v0
                    (d_find'45'thunk_204 (coe v0) (coe v1) (coe v5)) v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_flat'45'halt_854 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call-sv
d_do'45'call'45'sv_890 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'call'45'sv_890 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe du_flat'45'halt_854 (coe v3)
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    d_do'45'call'45'code_866 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                       (d_floc_80 (coe v3))
                       (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v5)))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v4
        -> coe du_flat'45'halt_854 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v4 v5 v6
        -> coe du_flat'45'halt_854 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v4
        -> coe du_flat'45'halt_854 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-call
d_do'45'call_914 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'call_914 v0 v1 v2
  = coe
      d_do'45'call'45'sv_890 (coe v0) (coe v1)
      (coe d_fclosure_88 (coe v2)) (coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.CallPost
d_CallPost_924 a0 a1 a2 = ()
data T_CallPost_924
  = C_cp'45'halt_930 |
    C_cp'45'enter_936 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 Integer
-- Once.CCC.Machine.Flat.FlatMachine.callView
d_callView_942 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_CallPost_924
d_callView_942 v0 v1 v2
  = coe
      du_go'45'sv_1050 (coe v0) (coe v1) (coe v2)
      (coe d_fclosure_88 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine._.go-at
d_go'45'at_958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  Maybe Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_924
d_go'45'at_958 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_go'45'at_958 v3 v5
du_go'45'at_958 ::
  Maybe Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_CallPost_924
du_go'45'at_958 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_cp'45'enter_936 v1 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_cp'45'halt_930
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-code
d_go'45'code_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_924
d_go'45'code_998 v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_go'45'code_998 v0 v1 v3
du_go'45'code_998 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CallPost_924
du_go'45'code_998 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
               -> coe C_cp'45'halt_930
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v4
               -> coe C_cp'45'halt_930
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v4 v5 v6
               -> coe C_cp'45'halt_930
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v4
               -> coe
                    du_go'45'at_958
                    (coe d_find'45'thunk_204 (coe v0) (coe v1) (coe v4)) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_cp'45'halt_930
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.go-sv
d_go'45'sv_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CallPost_924
d_go'45'sv_1050 v0 v1 v2 v3 ~v4 = du_go'45'sv_1050 v0 v1 v2 v3
du_go'45'sv_1050 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 ->
  T_CallPost_924
du_go'45'sv_1050 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Ptr_72 v4
        -> case coe v4 of
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtStack_16 v5 v6
               -> coe C_cp'45'halt_930
             MAlonzo.Code.Once.CCC.Machine.Locations.C_AtDynamic_18 v5
               -> coe
                    du_go'45'code_998 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                       (d_floc_80 (coe v2))
                       (MAlonzo.Code.Once.Memory.HeapAddress.d_sucHL_92 (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v4
        -> coe C_cp'45'halt_930
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_78 v4 v5 v6
        -> coe C_cp'45'halt_930
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Code_80 v4
        -> coe C_cp'45'halt_930
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-save-closure
d_do'45'save'45'closure_1072 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_68 -> T_FlatState_68
d_do'45'save'45'closure_1072 ~v0 v1
  = du_do'45'save'45'closure_1072 v1
du_do'45'save'45'closure_1072 :: T_FlatState_68 -> T_FlatState_68
du_do'45'save'45'closure_1072 v0
  = coe
      C_mkFlatFull_90 (coe d_floc_80 (coe v0)) (coe d_falloc_82 (coe v0))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v0)))
      (coe d_fret_86 (coe v0))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
            (coe d_floc_80 (coe v0)))
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56))
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_1076 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_FlatState_68
d_flat'45'exec'45'instr_1076 v0 v1
  = let v2
          = \ v2 v3 ->
              d_flat'45'step'45'straight_522 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2312 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_706
                     (coe v0) (coe v1) (coe d_enter'45'frame_528 (coe v0) (coe v3))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2314 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_706
                     (coe v0) (coe v1) (coe du_leave'45'frame_550) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2318 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_706
                     (coe v0) (coe v1)
                     (coe
                        d_enter'45'frame_528 (coe v0)
                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2320
           -> coe
                (\ v3 v4 ->
                   d_flat'45'step'45'frame_706
                     (coe v0) (coe v1) (coe du_leave'45'frame_550) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2322
           -> coe (\ v3 v4 -> d_do'45'call_914 (coe v0) (coe v3) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2344
           -> coe (\ v3 v4 -> coe du_do'45'save'45'closure_1072 (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2356 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2274 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            C_mkFlatFull_90 (coe d_floc_80 (coe v6)) (coe d_falloc_82 (coe v6))
                            (coe addInt (coe (1 :: Integer)) (coe d_fpc_84 (coe v6)))
                            (coe d_fret_86 (coe v6)) (coe d_fclosure_88 (coe v6)))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2276 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            du_do'45'jump_504 (d_find'45'label_158 (coe v0) (coe v5) (coe v4))
                            v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2278 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_512 v0
                            (coe
                               du_sv'45'is'45'zero_100
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                                     (coe d_floc_80 (coe v6)))
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2280 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_512 v0
                            (coe
                               du_tag'45'zf_102
                               (coe du_flat'45'read'45'tag_114 (coe d_floc_80 (coe v6))))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2282 v4 v5
                  -> coe (\ v6 v7 -> d_do'45'thunk_848 (coe v0) (coe v5) (coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2284 v4
                  -> coe (\ v5 v6 -> coe du_do'45'ret_714 (d_fret_86 (coe v6)) v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat
d_exec'45'flat_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_FlatState_68
d_exec'45'flat_1130 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_step'45'dispatch_1132 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                   (coe d_floc_80 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.step-dispatch
d_step'45'dispatch_1132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_FlatState_68
d_step'45'dispatch_1132 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else coe
             d_fetch'45'dispatch_1134 v0
             (coe du_fetch_210 (coe v3) (coe d_fpc_84 (coe v4))) v2 v3 v4
-- Once.CCC.Machine.Flat.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_1134 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> T_FlatState_68
d_fetch'45'dispatch_1134 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 v5 ->
                d_exec'45'flat_1130
                  (coe v0) (coe v3) (coe v4)
                  (coe d_flat'45'exec'45'instr_1076 v0 v2 v4 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_90
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                        (coe d_floc_80 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                        (coe d_floc_80 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                        (coe d_floc_80 (coe v4)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_82 (coe v4)) (coe d_fpc_84 (coe v4))
                  (coe d_fret_86 (coe v4)) (coe d_fclosure_88 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_1168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_1168 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_1192 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_1192 = erased
-- Once.CCC.Machine.Flat.FlatMachine.≡ᵇ-true
d_'8801''7495''45'true_1218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_1218 = erased
-- Once.CCC.Machine.Flat.FlatMachine.lab-eq
d_lab'45'eq_1230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_1230 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.just-inj
d_just'45'inj_1246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_1246 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-lands
d_fl'45'go'45'lands_1260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_1260 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'lands_1260 v0 v1 v2 v3 v4
du_fl'45'go'45'lands_1260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_1260 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_1312 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_118 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.step
d_step_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_1288 v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 ~v8
  = du_step_1288 v0 v2 v3 v4 v7
du_step_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_1288 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_fl'45'go'45'lands_1260 (coe v0) (coe v1) (coe v2)
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
d_go_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1312 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_go_1312 v0 v2 v3 v4 v5 v7
du_go_1312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1312 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_match_1336 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__140 (coe v6)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_step_1288 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._._.match
d_match_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_match_1336 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_match_1336 v0 v4 v5 v6 v7 v10
du_match_1336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_match_1336 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      else coe du_step_1288 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Machine.Flat.FlatMachine._._._.just-inj
d_just'45'inj_1350 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_1350 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-lands
d_find'45'label'45'lands_1376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_1376 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_1414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_1414 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightStep
d_StraightStep_1434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 -> ()
d_StraightStep_1434 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_1450 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_1450 = erased
-- Once.CCC.Machine.Flat.FlatMachine.Straight
d_Straight_1466 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] -> ()
d_Straight_1466 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-All
d_fetch'45'All_1476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_1476 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_fetch'45'All_1476 v2 v3 v5
du_fetch'45'All_1476 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_fetch'45'All_1476 v0 v1 v2
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
                         -> coe du_fetch'45'All_1476 (coe v4) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-Straight
d_fetch'45'Straight_1500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_1500 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_1522 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_FlatState_68 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
   T_FlatState_68 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (T_FlatState_68 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  T_FlatState_68 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_1522 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shift-loc
d_shift'45'loc_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_1642 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_shift'45'loc_1642 v0 v1 v3 v4 v5 v6
du_shift'45'loc_1642 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_1642 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v7
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v3) in
              coe
                (if coe v7
                   then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                   else (let v8 = coe du_fetch_210 (coe v2) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     du_shift'45'loc_1642 (coe v0) (coe v6) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2870
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe addInt (coe (1 :: Integer)) (coe v5))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_1770 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_1770 = erased
-- Once.CCC.Machine.Flat.FlatMachine.forced
d_forced_1790 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_forced_1790 ~v0 v1 = du_forced_1790 v1
du_forced_1790 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_forced_1790 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_1800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_1800 ~v0 v1 v2 ~v3 v4
  = du_exec'45'trace'45'is'45'flat_1800 v1 v2 v4
du_exec'45'trace'45'is'45'flat_1800 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2286] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_1800 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v1) in
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
