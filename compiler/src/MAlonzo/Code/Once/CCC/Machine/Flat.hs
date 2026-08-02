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
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace_58 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'trace_2818 (coe v0)
-- Once.CCC.Machine.Flat.FlatMachine.FlatState
d_FlatState_62 a0 = ()
data T_FlatState_62
  = C_mkFlat_76 MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
                MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 Integer
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.floc
d_floc_70 ::
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_floc_70 v0
  = case coe v0 of
      C_mkFlat_76 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.falloc
d_falloc_72 ::
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_falloc_72 v0
  = case coe v0 of
      C_mkFlat_76 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.FlatState.fpc
d_fpc_74 :: T_FlatState_62 -> Integer
d_fpc_74 v0
  = case coe v0 of
      C_mkFlat_76 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.sv-is-zero
d_sv'45'is'45'zero_78 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_sv'45'is'45'zero_78 ~v0 v1 = du_sv'45'is'45'zero_78 v1
du_sv'45'is'45'zero_78 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_sv'45'is'45'zero_78 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Tag_74 v2
           -> case coe v2 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.tag-zf
d_tag'45'zf_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
d_tag'45'zf_80 ~v0 v1 = du_tag'45'zf_80 v1
du_tag'45'zf_80 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68 -> Bool
du_tag'45'zf_80 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_sv'45'is'45'zero_78 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-at
d_flat'45'read'45'at_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'at_84 ~v0 v1 v2 = du_flat'45'read'45'at_84 v1 v2
du_flat'45'read'45'at_84 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'at_84 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_766 (coe v0)
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.flat-read-tag
d_flat'45'read'45'tag_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_flat'45'read'45'tag_92 ~v0 v1 = du_flat'45'read'45'tag_92 v1
du_flat'45'read'45'tag_92 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_flat'45'read'45'tag_92 v0
  = coe
      du_flat'45'read'45'at_84 (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.du_sv'45'as'45'loc_1396
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Input1_56)))
-- Once.CCC.Machine.Flat.FlatMachine.label-of?
d_label'45'of'63'_96 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe Integer
d_label'45'of'63'_96 ~v0 v1 = du_label'45'of'63'_96 v1
du_label'45'of'63'_96 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Maybe Integer
du_label'45'of'63'_96 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Machine.Flat.FlatMachine.fl-go
d_fl'45'go_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_100 v0 v1 v2 v3
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> let v6 = coe du_label'45'of'63'_96 (coe v4) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       d_fl'45'label'45'match_102 (coe v0) (coe eqInt (coe v7) (coe v2))
                       (coe v5) (coe v2) (coe v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       d_fl'45'go_100 (coe v0) (coe v5) (coe v2)
                       (coe addInt (coe (1 :: Integer)) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fl-label-match
d_fl'45'label'45'match_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_102 v0 v1 v2 v3 v4
  = if coe v1
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
      else coe
             d_fl'45'go_100 (coe v0) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
-- Once.CCC.Machine.Flat.FlatMachine.find-label
d_find'45'label_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> Maybe Integer
d_find'45'label_142 v0 v1 v2
  = coe
      d_fl'45'go_100 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
-- Once.CCC.Machine.Flat.FlatMachine.fetch
d_fetch_148 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_148 ~v0 v1 v2 = du_fetch_148 v1 v2
du_fetch_148 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_148 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe du_fetch_148 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-jump
d_do'45'jump_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe Integer -> T_FlatState_62 -> T_FlatState_62
d_do'45'jump_156 ~v0 v1 = du_do'45'jump_156 v1
du_do'45'jump_156 ::
  Maybe Integer -> T_FlatState_62 -> T_FlatState_62
du_do'45'jump_156 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 ->
                coe
                  C_mkFlat_76 (coe d_floc_70 (coe v2)) (coe d_falloc_72 (coe v2))
                  (coe v1))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 ->
                coe
                  C_mkFlat_76
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_560
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                        (coe d_floc_70 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554
                        (coe d_floc_70 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556
                        (coe d_floc_70 (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_72 (coe v1)) (coe d_fpc_74 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.do-branch
d_do'45'branch_164 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 -> T_FlatState_62
d_do'45'branch_164 v0 v1
  = if coe v1
      then coe
             (\ v2 v3 v4 ->
                coe
                  du_do'45'jump_156 (d_find'45'label_142 (coe v0) (coe v3) (coe v2))
                  v4)
      else coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlat_76 (coe d_floc_70 (coe v4)) (coe d_falloc_72 (coe v4))
                  (coe addInt (coe (1 :: Integer)) (coe d_fpc_74 (coe v4))))
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-straight
d_flat'45'step'45'straight_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  T_FlatState_62 -> T_FlatState_62
d_flat'45'step'45'straight_174 v0 v1 v2
  = coe
      C_mkFlat_76
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
            (coe v0) (coe v1) (coe d_floc_70 (coe v2))
            (coe d_falloc_72 (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
            (coe v0) (coe v1) (coe d_floc_70 (coe v2))
            (coe d_falloc_72 (coe v2))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_74 (coe v2)))
-- Once.CCC.Machine.Flat.FlatMachine.enter-frame
d_enter'45'frame_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_enter'45'frame_180 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714
      (coe
         MAlonzo.Code.Once.CCC.FrameSemantics.d_shift'45'frame_102 v0
         (MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v2))
         v1)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_current'45'frame_704
            (coe v2))
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
            (coe v2)))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
         (coe v2))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v2))
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-aux
d_leave'45'frame'45'aux_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_leave'45'frame'45'aux_186 ~v0 v1
  = du_leave'45'frame'45'aux_186 v1
du_leave'45'frame'45'aux_186 ::
  [AgdaAny] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_leave'45'frame'45'aux_186 v0
  = case coe v0 of
      [] -> coe (\ v1 -> v1)
      (:) v1 v2
        -> coe
             (\ v3 ->
                coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkAllocState_714 (coe v1)
                  (coe v2)
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'slot_708 (coe v3))
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_next'45'heap'45'ref_710
                     (coe v3))
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'size_712 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame
d_leave'45'frame_196 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
d_leave'45'frame_196 ~v0 v1 = du_leave'45'frame_196 v1
du_leave'45'frame_196 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626
du_leave'45'frame_196 v0
  = coe
      du_leave'45'frame'45'aux_186
      (MAlonzo.Code.Once.CCC.Machine.SMCore.d_saved'45'frames_706
         (coe v0))
      v0
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-next-slot
d_leave'45'frame'45'next'45'slot_202 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'next'45'slot_202 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_212 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_212 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-heap-ref
d_leave'45'frame'45'heap'45'ref_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'heap'45'ref_220 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_230 = erased
-- Once.CCC.Machine.Flat.FlatMachine.leave-frame-block-size
d_leave'45'frame'45'block'45'size_238 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leave'45'frame'45'block'45'size_238 = erased
-- Once.CCC.Machine.Flat.FlatMachine._.go
d_go_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_248 = erased
-- Once.CCC.Machine.Flat.FlatMachine.flat-step-frame
d_flat'45'step'45'frame_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626) ->
  T_FlatState_62 -> T_FlatState_62
d_flat'45'step'45'frame_254 v0 v1 v2 v3
  = coe
      C_mkFlat_76
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
            (coe v0) (coe v1) (coe d_floc_70 (coe v3))
            (coe d_falloc_72 (coe v3))))
      (coe
         v2
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
               (coe v0) (coe v1) (coe d_floc_70 (coe v3))
               (coe d_falloc_72 (coe v3)))))
      (coe addInt (coe (1 :: Integer)) (coe d_fpc_74 (coe v3)))
-- Once.CCC.Machine.Flat.FlatMachine.flat-exec-instr
d_flat'45'exec'45'instr_262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 -> T_FlatState_62
d_flat'45'exec'45'instr_262 v0 v1
  = let v2
          = \ v2 v3 ->
              d_flat'45'step'45'straight_174 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2264 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_254
                     (coe v0) (coe v1) (coe d_enter'45'frame_180 (coe v0) (coe v3))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2266 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_254
                     (coe v0) (coe v1) (coe du_leave'45'frame_196) (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2270 v3
           -> coe
                (\ v4 v5 ->
                   d_flat'45'step'45'frame_254
                     (coe v0) (coe v1)
                     (coe
                        d_enter'45'frame_180 (coe v0)
                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                     (coe v5))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2272
           -> coe
                (\ v3 v4 ->
                   d_flat'45'step'45'frame_254
                     (coe v0) (coe v1) (coe du_leave'45'frame_196) (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2308 v3
           -> case coe v3 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2230 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            C_mkFlat_76 (coe d_floc_70 (coe v6)) (coe d_falloc_72 (coe v6))
                            (coe addInt (coe (1 :: Integer)) (coe d_fpc_74 (coe v6))))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2232 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            du_do'45'jump_156 (d_find'45'label_142 (coe v0) (coe v5) (coe v4))
                            v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2234 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_164 v0
                            (coe
                               du_sv'45'is'45'zero_78
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg_158
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                                     (coe d_floc_70 (coe v6)))
                                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_Scratch_62)))
                            v4 v5 v6)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2236 v4
                  -> coe
                       (\ v5 v6 ->
                          coe
                            d_do'45'branch_164 v0
                            (coe
                               du_tag'45'zf_80
                               (coe du_flat'45'read'45'tag_92 (coe d_floc_70 (coe v6))))
                            v4 v5 v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat
d_exec'45'flat_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 -> T_FlatState_62
d_exec'45'flat_302 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                d_step'45'dispatch_304 (coe v0)
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558
                   (coe d_floc_70 (coe v3)))
                (coe v4) (coe v2) (coe v3))
-- Once.CCC.Machine.Flat.FlatMachine.step-dispatch
d_step'45'dispatch_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 -> T_FlatState_62
d_step'45'dispatch_304 v0 v1 v2 v3 v4
  = if coe v1
      then coe v4
      else coe
             d_fetch'45'dispatch_306 v0
             (coe du_fetch_148 (coe v3) (coe d_fpc_74 (coe v4))) v2 v3 v4
-- Once.CCC.Machine.Flat.FlatMachine.fetch-dispatch
d_fetch'45'dispatch_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 -> T_FlatState_62
d_fetch'45'dispatch_306 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             (\ v3 v4 v5 ->
                d_exec'45'flat_302
                  (coe v0) (coe v3) (coe v4)
                  (coe d_flat'45'exec'45'instr_262 v0 v2 v4 v5))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v2 v3 v4 ->
                coe
                  C_mkFlat_76
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_560
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552
                        (coe d_floc_70 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554
                        (coe d_floc_70 (coe v4)))
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556
                        (coe d_floc_70 (coe v4)))
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                  (coe d_falloc_72 (coe v4)) (coe d_fpc_74 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-halted
d_exec'45'flat'45'halted_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'halted_340 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-step
d_exec'45'flat'45'step_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'step_364 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-offend
d_exec'45'flat'45'offend_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'offend_392 = erased
-- Once.CCC.Machine.Flat.FlatMachine.StraightStep
d_StraightStep_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 -> ()
d_StraightStep_412 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-straight-step
d_exec'45'flat'45'straight'45'step_428 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'straight'45'step_428 = erased
-- Once.CCC.Machine.Flat.FlatMachine.Straight
d_Straight_444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_Straight_444 = erased
-- Once.CCC.Machine.Flat.FlatMachine.fetch-All
d_fetch'45'All_454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_fetch'45'All_454 ~v0 ~v1 v2 v3 ~v4 v5 ~v6
  = du_fetch'45'All_454 v2 v3 v5
du_fetch'45'All_454 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_fetch'45'All_454 v0 v1 v2
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
                         -> coe du_fetch'45'All_454 (coe v4) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.Flat.FlatMachine.fetch-Straight
d_fetch'45'Straight_478 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  T_FlatState_62 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'Straight_478 = erased
-- Once.CCC.Machine.Flat.FlatMachine.exec-flat-invariant
d_exec'45'flat'45'invariant_500 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (T_FlatState_62 -> AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   ()) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
   T_FlatState_62 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (T_FlatState_62 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Integer ->
  T_FlatState_62 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'flat'45'invariant_500 = erased
-- Once.CCC.Machine.Flat.FlatMachine.shift-loc
d_shift'45'loc_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_shift'45'loc_620 v0 v1 ~v2 v3 v4 v5 v6 ~v7
  = du_shift'45'loc_620 v0 v1 v3 v4 v5 v6
du_shift'45'loc_620 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_shift'45'loc_620 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v7
                    = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v3) in
              coe
                (if coe v7
                   then coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                   else (let v8 = coe du_fetch_148 (coe v2) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                -> coe
                                     du_shift'45'loc_620 (coe v0) (coe v6) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.d_exec'45'abstract_2816
                                           (coe v0) (coe v9) (coe v3) (coe v4)))
                                     (coe addInt (coe (1 :: Integer)) (coe v5))
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                              _ -> MAlonzo.RTE.mazUnreachableError))))
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-halted
d_exec'45'trace'45'halted_748 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exec'45'trace'45'halted_748 = erased
-- Once.CCC.Machine.Flat.FlatMachine.forced
d_forced_768 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
d_forced_768 ~v0 v1 = du_forced_768 v1
du_forced_768 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540
du_forced_768 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mkLocState_560
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_regs_552 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_stackMem_554 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.d_heapMem_556 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.CCC.Machine.Flat.FlatMachine.exec-trace-is-flat
d_exec'45'trace'45'is'45'flat_778 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_626 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exec'45'trace'45'is'45'flat_778 ~v0 v1 v2 ~v3 v4
  = du_exec'45'trace'45'is'45'flat_778 v1 v2 v4
du_exec'45'trace'45'is'45'flat_778 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_540 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exec'45'trace'45'is'45'flat_778 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.CCC.Machine.SMCore.d_halted_558 (coe v1) in
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
