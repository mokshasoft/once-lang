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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Machine.Flat.FlatMachine._.exec-trace
d_exec'45'trace_52 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_52 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2550 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState
d_FlatState_56 a0 = ()
data T_FlatState_56
  = C_mkFlat_70 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
                MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 Integer
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.floc
d_floc_64 ::
  T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_floc_64 v0
  = case coe v0 of
      C_mkFlat_70 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.falloc
d_falloc_66 ::
  T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510
d_falloc_66 v0
  = case coe v0 of
      C_mkFlat_70 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fpc
d_fpc_68 :: T_FlatState_56 -> Integer
d_fpc_68 v0
  = case coe v0 of
      C_mkFlat_70 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_72 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_sv'45'is'45'zero_72 ~v0 v1 = du_sv'45'is'45'zero_72 v1
du_sv'45'is'45'zero_72 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_sv'45'is'45'zero_72 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_72 v2
           -> case coe v2 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.tag-zf
d_tag'45'zf_74 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
d_tag'45'zf_74 ~v0 v1 = du_tag'45'zf_74 v1
du_tag'45'zf_74 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Bool
du_tag'45'zf_74 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'is'45'zero_72 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-at
d_flat'45'read'45'at_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'at_78 ~v0 v1 v2 = du_flat'45'read'45'at_78 v1 v2
du_flat'45'read'45'at_78 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'at_78 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_618 (coe v0)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_flat'45'read'45'tag_86 ~v0 v1 = du_flat'45'read'45'tag_86 v1
du_flat'45'read'45'tag_86 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_flat'45'read'45'tag_86 v0
  = coe
      du_flat'45'read'45'at_78 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1206
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v0))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
-- Once.CCC.Machine.Flat.FlatMachine.label-of?
d_label'45'of'63'_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  Maybe Integer
d_label'45'of'63'_90 ~v0 v1 = du_label'45'of'63'_90 v1
du_label'45'of'63'_90 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  Maybe Integer
du_label'45'of'63'_90 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2118 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2040 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.fl-go
d_fl'45'go_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_94 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> let v6 = coe du_label'45'of'63'_90 (coe v4) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       d_fl'45'label'45'match_96 (coe v0) (coe eqInt (coe v7) (coe v2))
                       (coe v5) (coe v2) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       d_fl'45'go_94 (coe v0) (coe v5) (coe v2)
                       (coe addInt (coe (1 :: Integer)) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-label-match
d_fl'45'label'45'match_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_96 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_fl'45'go_94 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-label
d_find'45'label_136 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer -> Maybe Integer
d_find'45'label_136 v0 v1 v2
  = coe d_fl'45'go_94 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.fetch
d_fetch_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048
d_fetch_142 ~v0 v1 v2 = du_fetch_142 v1 v2
du_fetch_142 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048
du_fetch_142 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_fetch_142 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-jump
d_do'45'jump_150 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_56 -> T_FlatState_56
d_do'45'jump_150 ~v0 v1 = du_do'45'jump_150 v1
du_do'45'jump_150 ::
  Maybe Integer -> T_FlatState_56 -> T_FlatState_56
du_do'45'jump_150 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  C_mkFlat_70 (coe d_floc_64 (coe v2)) (coe d_falloc_66 (coe v2))
                  (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  C_mkFlat_70
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
                        (coe d_floc_64 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
                        (coe d_floc_64 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
                        (coe d_floc_64 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_66 (coe v1)) (coe d_fpc_68 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-branch
d_do'45'branch_158 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 -> T_FlatState_56
d_do'45'branch_158 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 ->
                coe
                  du_do'45'jump_150 (d_find'45'label_136 (coe v0) (coe v3) (coe v2))
                  v4)
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlat_70 (coe d_floc_64 (coe v4)) (coe d_falloc_66 (coe v4))
                  (coe addInt (coe (1 :: Integer)) (coe d_fpc_68 (coe v4))))
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  T_FlatState_56 -> T_FlatState_56
d_flat'45'step'45'straight_168 v0 v1 v2
  = coe
      C_mkFlat_70
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2548
            (coe v0) (coe v1) (coe d_floc_64 (coe v2))
            (coe d_falloc_66 (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2548
            (coe v0) (coe v1) (coe d_floc_64 (coe v2))
            (coe d_falloc_66 (coe v2))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_68 (coe v2)))
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 -> T_FlatState_56
d_flat'45'exec'45'instr_174 v0 v1
  = let v2
          = \ v2 v3 ->
              d_flat'45'step'45'straight_168 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2118 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2040 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            C_mkFlat_70 (coe d_floc_64 (coe v6)) (coe d_falloc_66 (coe v6))
                            (coe addInt (coe (1 :: Integer)) (coe d_fpc_68 (coe v6))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2042 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            du_do'45'jump_150 (d_find'45'label_136 (coe v0) (coe v5) (coe v4))
                            v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2044 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_158 v0
                            (coe
                               du_sv'45'is'45'zero_72
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_152
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
                                     (coe d_floc_64 (coe v6)))
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2046 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_158 v0
                            (coe
                               du_tag'45'zf_74
                               (coe du_flat'45'read'45'tag_86 (coe d_floc_64 (coe v6))))
                            v4 v5 v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat
d_exec'45'flat_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 -> T_FlatState_56
d_exec'45'flat_200 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_step'45'dispatch_202 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474
                   (coe d_floc_64 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.step-dispatch
d_step'45'dispatch_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 -> T_FlatState_56
d_step'45'dispatch_202 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else coe
             d_fetch'45'dispatch_204 v0
             (coe du_fetch_142 (coe v3) (coe d_fpc_68 (coe v4))) v2 v3 v4
-- Once.CCC.Machine.Flat.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_204 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 -> T_FlatState_56
d_fetch'45'dispatch_204 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 v5 ->
                d_exec'45'flat_200
                  (coe v0) (coe v3) (coe v4)
                  (coe d_flat'45'exec'45'instr_174 v0 v2 v4 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlat_70
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468
                        (coe d_floc_64 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470
                        (coe d_floc_64 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472
                        (coe d_floc_64 (coe v4)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_66 (coe v4)) (coe d_fpc_68 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_238 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_262 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_290 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightStep
d_StraightStep_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 -> ()
d_StraightStep_310 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
   T_FlatState_56 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_326 = erased
-- Once.CCC.Machine.Flat.FlatMachine.Straight
d_Straight_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] -> ()
d_Straight_342 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-All
d_fetch'45'All_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_352 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_fetch'45'All_352 v2 v3 v5
du_fetch'45'All_352 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_fetch'45'All_352 v0 v1 v2
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
                         -> coe du_fetch'45'All_352 (coe v4) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-Straight
d_fetch'45'Straight_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  T_FlatState_56 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_376 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_FlatState_56 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
   T_FlatState_56 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (T_FlatState_56 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  T_FlatState_56 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_398 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shift-loc
d_shift'45'loc_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_518 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_shift'45'loc_518 v0 v1 v3 v4 v5 v6
du_shift'45'loc_518 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_518 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v7
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474 (coe v3) in
              coe
                (if coe v7
                   then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                   else (let v8 = coe du_fetch_142 (coe v2) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     du_shift'45'loc_518 (coe v0) (coe v6) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2548
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2548
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe addInt (coe (1 :: Integer)) (coe v5))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_646 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_646 = erased
-- Once.CCC.Machine.Flat.FlatMachine.forced
d_forced_666 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
d_forced_666 ~v0 v1 = du_forced_666 v1
du_forced_666 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456
du_forced_666 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_476
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_468 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_470 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_472 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_676 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_510 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_676 ~v0 v1 v2 ~v3 v4
  = du_exec'45'trace'45'is'45'flat_676 v1 v2 v4
du_exec'45'trace'45'is'45'flat_676 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2048] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_456 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_676 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_474 (coe v1) in
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
