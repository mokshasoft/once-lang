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
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Machine.Flat.FlatMachine._.exec-trace
d_exec'45'trace_58 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2768 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState
d_FlatState_62 a0 = ()
data T_FlatState_62
  = C_mkFlatFull_84 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
                    MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 Integer
                    [Integer] MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.floc
d_floc_74 ::
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_floc_74 v0
  = case coe v0 of
      C_mkFlatFull_84 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.falloc
d_falloc_76 ::
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_falloc_76 v0
  = case coe v0 of
      C_mkFlatFull_84 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fpc
d_fpc_78 :: T_FlatState_62 -> Integer
d_fpc_78 v0
  = case coe v0 of
      C_mkFlatFull_84 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fret
d_fret_80 :: T_FlatState_62 -> [Integer]
d_fret_80 v0
  = case coe v0 of
      C_mkFlatFull_84 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fclosure
d_fclosure_82 ::
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_fclosure_82 v0
  = case coe v0 of
      C_mkFlatFull_84 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.mkFlat
d_mkFlat_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> T_FlatState_62
d_mkFlat_86 v0 v1 v2
  = coe
      C_mkFlatFull_84 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74
         (coe (0 :: Integer)))
-- Once.CCC.Machine.Flat.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_94 ~v0 v1 = du_sv'45'is'45'zero_94 v1
du_sv'45'is'45'zero_94 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_94 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v2
           -> case coe v2 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.tag-zf
d_tag'45'zf_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_tag'45'zf_96 ~v0 v1 = du_tag'45'zf_96 v1
du_tag'45'zf_96 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_tag'45'zf_96 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'is'45'zero_94 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-at
d_flat'45'read'45'at_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'at_100 ~v0 v1 v2
  = du_flat'45'read'45'at_100 v1 v2
du_flat'45'read'45'at_100 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'at_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712 (coe v0)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_108 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'tag_108 ~v0 v1 = du_flat'45'read'45'tag_108 v1
du_flat'45'read'45'tag_108 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'tag_108 v0
  = coe
      du_flat'45'read'45'at_100 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1342
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
-- Once.CCC.Machine.Flat.FlatMachine.label-of?
d_label'45'of'63'_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe Integer
d_label'45'of'63'_112 ~v0 v1 = du_label'45'of'63'_112 v1
du_label'45'of'63'_112 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe Integer
du_label'45'of'63'_112 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.fl-go
d_fl'45'go_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_116 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> let v6 = coe du_label'45'of'63'_112 (coe v4) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       d_fl'45'label'45'match_118 (coe v0) (coe eqInt (coe v7) (coe v2))
                       (coe v5) (coe v2) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       d_fl'45'go_116 (coe v0) (coe v5) (coe v2)
                       (coe addInt (coe (1 :: Integer)) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-label-match
d_fl'45'label'45'match_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_118 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_fl'45'go_116 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-label
d_find'45'label_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
d_find'45'label_158 v0 v1 v2
  = coe
      d_fl'45'go_116 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.thunk-of?
d_thunk'45'of'63'_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe Integer
d_thunk'45'of'63'_164 ~v0 v1 = du_thunk'45'of'63'_164 v1
du_thunk'45'of'63'_164 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Maybe Integer
du_thunk'45'of'63'_164 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v3 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.ft-go
d_ft'45'go_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_ft'45'go_168 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> let v6 = coe du_thunk'45'of'63'_164 (coe v4) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       d_ft'45'match_170 (coe v0) (coe eqInt (coe v7) (coe v2)) (coe v5)
                       (coe v2) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       d_ft'45'go_168 (coe v0) (coe v5) (coe v2)
                       (coe addInt (coe (1 :: Integer)) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.ft-match
d_ft'45'match_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_ft'45'match_170 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_ft'45'go_168 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-thunk
d_find'45'thunk_210 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Maybe Integer
d_find'45'thunk_210 v0 v1 v2
  = coe
      d_ft'45'go_168 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.fetch
d_fetch_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_216 ~v0 v1 v2 = du_fetch_216 v1 v2
du_fetch_216 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_216 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_fetch_216 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-jump
d_do'45'jump_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_62 -> T_FlatState_62
d_do'45'jump_224 ~v0 v1 = du_do'45'jump_224 v1
du_do'45'jump_224 ::
  Maybe Integer -> T_FlatState_62 -> T_FlatState_62
du_do'45'jump_224 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  C_mkFlatFull_84 (coe d_floc_74 (coe v2)) (coe d_falloc_76 (coe v2))
                  (coe v1) (coe d_fret_80 (coe v2)) (coe d_fclosure_82 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_84
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                        (coe d_floc_74 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                        (coe d_floc_74 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                        (coe d_floc_74 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_76 (coe v1)) (coe d_fpc_78 (coe v1))
                  (coe d_fret_80 (coe v1)) (coe d_fclosure_82 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-branch
d_do'45'branch_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 -> T_FlatState_62
d_do'45'branch_232 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 ->
                coe
                  du_do'45'jump_224 (d_find'45'label_158 (coe v0) (coe v3) (coe v2))
                  v4)
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_84 (coe d_floc_74 (coe v4)) (coe d_falloc_76 (coe v4))
                  (coe addInt (coe (1 :: Integer)) (coe d_fpc_78 (coe v4)))
                  (coe d_fret_80 (coe v4)) (coe d_fclosure_82 (coe v4)))
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_FlatState_62 -> T_FlatState_62
d_flat'45'step'45'straight_242 v0 v1 v2
  = coe
      C_mkFlatFull_84
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
            (coe v0) (coe v1) (coe d_floc_74 (coe v2))
            (coe d_falloc_76 (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
            (coe v0) (coe v1) (coe d_floc_74 (coe v2))
            (coe d_falloc_76 (coe v2))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_78 (coe v2)))
      (coe d_fret_80 (coe v2)) (coe d_fclosure_82 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.enter-frame
d_enter'45'frame_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_enter'45'frame_248 v0 v1 v2
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
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame'45'aux_254 ~v0 v1
  = du_leave'45'frame'45'aux_254 v1
du_leave'45'frame'45'aux_254 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame'45'aux_254 v0
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
d_leave'45'frame_266 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_leave'45'frame_266 ~v0 v1 = du_leave'45'frame_266 v1
du_leave'45'frame_266 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
du_leave'45'frame_266 v0
  = coe
      du_leave'45'frame'45'aux_254
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_650
         (coe v0))
      v0
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-[]
d_leave'45'frame'45'slots'45''91''93'_272 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''91''93'_272 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-slots-∷
d_leave'45'frame'45'slots'45''8759'_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'slots'45''8759'_290 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-[]
d_leave'45'frame'45'saved'45''91''93'_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''91''93'_308 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_320 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_absurd_336
du_absurd_336 :: AgdaAny
du_absurd_336 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-saved-∷
d_leave'45'frame'45'saved'45''8759'_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'saved'45''8759'_346 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_364 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_374 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_384 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_394 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_404 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_414 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_414 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_422 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568) ->
  T_FlatState_62 -> T_FlatState_62
d_flat'45'step'45'frame_422 v0 v1 v2 v3
  = coe
      C_mkFlatFull_84
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
            (coe v0) (coe v1) (coe d_floc_74 (coe v3))
            (coe d_falloc_76 (coe v3))))
      (coe
         v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
               (coe v0) (coe v1) (coe d_floc_74 (coe v3))
               (coe d_falloc_76 (coe v3)))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_78 (coe v3)))
      (coe d_fret_80 (coe v3)) (coe d_fclosure_82 (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.do-ret
d_do'45'ret_430 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [Integer] -> T_FlatState_62 -> T_FlatState_62
d_do'45'ret_430 ~v0 v1 = du_do'45'ret_430 v1
du_do'45'ret_430 :: [Integer] -> T_FlatState_62 -> T_FlatState_62
du_do'45'ret_430 v0
  = case coe v0 of
      []
        -> coe
             (\ v1 ->
                coe
                  C_mkFlatFull_84
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                        (coe d_floc_74 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                        (coe d_floc_74 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                        (coe d_floc_74 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe du_leave'45'frame_266 (coe d_falloc_76 (coe v1)))
                  (coe d_fpc_78 (coe v1)) (coe d_fret_80 (coe v1))
                  (coe d_fclosure_82 (coe v1)))
      (:) v1 v2
        -> coe
             (\ v3 ->
                coe
                  C_mkFlatFull_84 (coe d_floc_74 (coe v3))
                  (coe du_leave'45'frame_266 (coe d_falloc_76 (coe v3))) (coe v1)
                  (coe v2) (coe d_fclosure_82 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-[]
d_do'45'ret'45'pc'45''91''93'_442 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''91''93'_442 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_454 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_468 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_absurd_468
du_absurd_468 :: AgdaAny
du_absurd_468 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-pc-∷
d_do'45'ret'45'pc'45''8759'_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'pc'45''8759'_476 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-[]
d_do'45'ret'45'fret'45''91''93'_492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''91''93'_492 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_504 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_504 = erased
-- Once.CCC.Machine.Flat.FlatMachine._._.absurd
d_absurd_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_absurd_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_absurd_518
du_absurd_518 :: AgdaAny
du_absurd_518 = MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-fret-∷
d_do'45'ret'45'fret'45''8759'_526 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'fret'45''8759'_526 = erased
-- Once.CCC.Machine.Flat.FlatMachine.do-ret-alloc
d_do'45'ret'45'alloc_542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_do'45'ret'45'alloc_542 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_552 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  T_FlatState_62 ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_552 = erased
-- Once.CCC.Machine.Flat.FlatMachine.grow-frame
d_grow'45'frame_558 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568
d_grow'45'frame_558 v0 v1 v2
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
d_do'45'thunk_564 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer -> T_FlatState_62 -> T_FlatState_62
d_do'45'thunk_564 v0 v1 v2
  = coe
      C_mkFlatFull_84 (coe d_floc_74 (coe v2))
      (coe
         d_grow'45'frame_558 (coe v0) (coe v1) (coe d_falloc_76 (coe v2)))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_78 (coe v2)))
      (coe d_fret_80 (coe v2)) (coe d_fclosure_82 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 -> T_FlatState_62
d_flat'45'exec'45'instr_570 v0 v1
  = let v2
          = \ v2 v3 ->
              d_flat'45'step'45'straight_242 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_422
                     (coe v0) (coe v1) (coe d_enter'45'frame_248 (coe v0) (coe v3))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_422
                     (coe v0) (coe v1) (coe du_leave'45'frame_266) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_422
                     (coe v0) (coe v1)
                     (coe
                        d_enter'45'frame_248 (coe v0)
                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
           -> coe
                (\ v3 v4 ->
                   d_flat'45'step'45'frame_422
                     (coe v0) (coe v1) (coe du_leave'45'frame_266) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            C_mkFlatFull_84 (coe d_floc_74 (coe v6)) (coe d_falloc_76 (coe v6))
                            (coe addInt (coe (1 :: Integer)) (coe d_fpc_78 (coe v6)))
                            (coe d_fret_80 (coe v6)) (coe d_fclosure_82 (coe v6)))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            du_do'45'jump_224 (d_find'45'label_158 (coe v0) (coe v5) (coe v4))
                            v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_232 v0
                            (coe
                               du_sv'45'is'45'zero_94
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_154
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                                     (coe d_floc_74 (coe v6)))
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_232 v0
                            (coe
                               du_tag'45'zf_96
                               (coe du_flat'45'read'45'tag_108 (coe d_floc_74 (coe v6))))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v4 v5
                  -> coe (\ v6 v7 -> d_do'45'thunk_564 (coe v0) (coe v5) (coe v7))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v4
                  -> coe (\ v5 v6 -> coe du_do'45'ret_430 (d_fret_80 (coe v6)) v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat
d_exec'45'flat_618 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 -> T_FlatState_62
d_exec'45'flat_618 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_step'45'dispatch_620 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500
                   (coe d_floc_74 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.step-dispatch
d_step'45'dispatch_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 -> T_FlatState_62
d_step'45'dispatch_620 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else coe
             d_fetch'45'dispatch_622 v0
             (coe du_fetch_216 (coe v3) (coe d_fpc_78 (coe v4))) v2 v3 v4
-- Once.CCC.Machine.Flat.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_622 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 -> T_FlatState_62
d_fetch'45'dispatch_622 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 v5 ->
                d_exec'45'flat_618
                  (coe v0) (coe v3) (coe v4)
                  (coe d_flat'45'exec'45'instr_570 v0 v2 v4 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlatFull_84
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494
                        (coe d_floc_74 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496
                        (coe d_floc_74 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498
                        (coe d_floc_74 (coe v4)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_76 (coe v4)) (coe d_fpc_78 (coe v4))
                  (coe d_fret_80 (coe v4)) (coe d_fclosure_82 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_656 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_656 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_680 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_680 = erased
-- Once.CCC.Machine.Flat.FlatMachine.≡ᵇ-true
d_'8801''7495''45'true_706 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'true_706 = erased
-- Once.CCC.Machine.Flat.FlatMachine.lab-eq
d_lab'45'eq_718 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lab'45'eq_718 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.just-inj
d_just'45'inj_734 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_734 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fl-go-lands
d_fl'45'go'45'lands_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fl'45'go'45'lands_748 v0 v1 v2 v3 v4 ~v5
  = du_fl'45'go'45'lands_748 v0 v1 v2 v3 v4
du_fl'45'go'45'lands_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fl'45'go'45'lands_748 v0 v1 v2 v3 v4
  = case coe v1 of
      (:) v5 v6
        -> coe
             du_go_800 (coe v0) (coe v6) (coe v2) (coe v3) (coe v4)
             (coe du_label'45'of'63'_112 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._.step
d_step_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_776 v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 ~v8
  = du_step_776 v0 v2 v3 v4 v7
du_step_776 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_776 v0 v1 v2 v3 v4
  = let v5
          = coe
              du_fl'45'go'45'lands_748 (coe v0) (coe v1) (coe v2)
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
d_go_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_800 v0 ~v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9
  = du_go_800 v0 v2 v3 v4 v5 v7
du_go_800 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer -> Maybe Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_800 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_match_824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe eqInt (coe v6) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_step_776 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine._._.match
d_match_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_match_824 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_match_824 v0 v4 v5 v6 v7 v10
du_match_824 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_match_824 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      else coe du_step_776 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Machine.Flat.FlatMachine._._._.just-inj
d_just'45'inj_838 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_838 = erased
-- Once.CCC.Machine.Flat.FlatMachine.find-label-lands
d_find'45'label'45'lands_864 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'lands_864 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_902 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_902 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightStep
d_StraightStep_922 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 -> ()
d_StraightStep_922 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_938 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_938 = erased
-- Once.CCC.Machine.Flat.FlatMachine.Straight
d_Straight_954 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] -> ()
d_Straight_954 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-All
d_fetch'45'All_964 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_964 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_fetch'45'All_964 v2 v3 v5
du_fetch'45'All_964 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_fetch'45'All_964 v0 v1 v2
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
                         -> coe du_fetch'45'All_964 (coe v4) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-Straight
d_fetch'45'Straight_988 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  T_FlatState_62 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_988 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_1010 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_FlatState_62 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   T_FlatState_62 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  T_FlatState_62 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_1010 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shift-loc
d_shift'45'loc_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_1130 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_shift'45'loc_1130 v0 v1 v3 v4 v5 v6
du_shift'45'loc_1130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_1130 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v7
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_500 (coe v3) in
              coe
                (if coe v7
                   then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                   else (let v8 = coe du_fetch_216 (coe v2) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     du_shift'45'loc_1130 (coe v0) (coe v6) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2766
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe addInt (coe (1 :: Integer)) (coe v5))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_1258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_1258 = erased
-- Once.CCC.Machine.Flat.FlatMachine.forced
d_forced_1278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
d_forced_1278 ~v0 v1 = du_forced_1278 v1
du_forced_1278 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482
du_forced_1278 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_502
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_494 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_496 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_498 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_1288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_1288 ~v0 v1 v2 ~v3 v4
  = du_exec'45'trace'45'is'45'flat_1288 v1 v2 v4
du_exec'45'trace'45'is'45'flat_1288 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_1288 v0 v1 v2
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
